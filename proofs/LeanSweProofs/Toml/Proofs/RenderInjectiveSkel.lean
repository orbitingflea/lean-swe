import LeanSweProofs.Toml.Model

/-!
# Provenance Skeleton Determinism & Equivalence for `Toml.Model.render`

Proves `Impl`-independent determinism of `SkeletonNode` updates (`insertDottedAndLookup`,
`applyHeaderSkel`, `insertAtActiveAndLookup`) and shows that two `TomlTable` entry lists
covered by the same skeleton with `TomlEquiv` leaf/inline-table values satisfy `TomlTableEquivList`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model

/-- Check whether `k` appears as a key in a `SkeletonNode` association list. -/
def skelHasKey (k : String) : List (String × SkeletonNode) → Bool
  | [] => false
  | (k', _) :: rest => k == k' || skelHasKey k rest

mutual
  /-- Computable pairwise-distinct-key check across a `SkeletonNode` tree. -/
  def skelNodeWF : SkeletonNode → Bool
    | .leaf => true
    | .inlineTable => true
    | .table _ sub => skelEntriesWF sub
    | .aot elems => skelAotWF elems
  termination_by sn => sizeOf sn
  decreasing_by all_goals simp +arith

  /-- Check pairwise distinct keys and recursively well-formed child skeletons. -/
  def skelEntriesWF : List (String × SkeletonNode) → Bool
    | [] => true
    | (k, sn) :: rest => !skelHasKey k rest && skelNodeWF sn && skelEntriesWF rest
  termination_by skel => sizeOf skel
  decreasing_by all_goals simp +arith

  /-- Check each element skeleton in an `[[aot]]` list satisfies `skelEntriesWF`. -/
  def skelAotWF : List (List (String × SkeletonNode)) → Bool
    | [] => true
    | e :: rest => skelEntriesWF e && skelAotWF rest
  termination_by elems => sizeOf elems
  decreasing_by all_goals simp +arith
end

private theorem skelHasKey_assocSetSkel (k k' : String) (v : SkeletonNode) :
    ∀ skel : List (String × SkeletonNode),
      skelHasKey k (assocSetSkel k' v skel) = (k == k' || skelHasKey k skel)
  | [] => by simp [assocSetSkel, skelHasKey]
  | (kh, vh) :: tl => by
    simp only [assocSetSkel]
    by_cases h : (k' == kh) = true
    · have hk := eq_of_beq h; subst hk; simp [skelHasKey]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, skelHasKey, skelHasKey_assocSetSkel k k' v tl]
      cases (k == kh) <;> cases (k == k') <;> rfl

theorem skelEntriesWF_assocSetSkel {k : String} {v : SkeletonNode} {skel : List (String × SkeletonNode)}
    (hs : skelEntriesWF skel = true) (hv : skelNodeWF v = true) :
    skelEntriesWF (assocSetSkel k v skel) = true := by
  induction skel with
  | nil => simp [assocSetSkel, skelEntriesWF, skelHasKey, hv]
  | cons hd tl ih =>
    rcases hd with ⟨kh, vh⟩
    simp only [skelEntriesWF, Bool.and_eq_true, Bool.not_eq_true'] at hs
    simp only [assocSetSkel]
    by_cases h : (k == kh) = true
    · simp [h, skelEntriesWF, hs.1.1, hv, hs.2]
    · have hkh : (kh == k) = false := by
        cases h2 : (kh == k)
        · rfl
        · have heq := eq_of_beq h2; subst heq; simp at h
      simp [h, skelEntriesWF, skelHasKey_assocSetSkel, hkh, hs.1.1, hs.1.2, ih hs.2]

theorem assocLookupSkel_wf {k : String} {skel : List (String × SkeletonNode)} {sn : SkeletonNode}
    (hs : skelEntriesWF skel = true) (hl : assocLookupSkel k skel = some sn) :
    skelNodeWF sn = true := by
  induction skel with
  | nil => simp [assocLookupSkel] at hl
  | cons hd tl ih =>
    rcases hd with ⟨kh, vh⟩
    simp only [skelEntriesWF, Bool.and_eq_true] at hs
    simp only [assocLookupSkel] at hl
    split at hl
    · injection hl with h; subst h; exact hs.1.2
    · exact ih hs.2 hl

theorem assocLookupSkel_sizeOf_lt {k : String} {sn : SkeletonNode} :
    ∀ skel : List (String × SkeletonNode),
      assocLookupSkel k skel = some sn → sizeOf sn < sizeOf skel
  | [], h => nomatch h
  | (kh, vh) :: tl, h => by
    simp only [assocLookupSkel] at h
    split at h
    · injection h with e; subst e; simp +arith
    · have ih := assocLookupSkel_sizeOf_lt tl h
      simp +arith at ih ⊢; omega

theorem assocLookupSkel_assocSetSkel (q k : String) (v : SkeletonNode) :
    ∀ skel : List (String × SkeletonNode),
      assocLookupSkel q (assocSetSkel k v skel) = if q == k then some v else assocLookupSkel q skel
  | [] => by simp [assocSetSkel, assocLookupSkel]
  | (kh, vh) :: tl => by
    simp only [assocSetSkel]
    by_cases h : (k == kh) = true
    · have hk := eq_of_beq h; subst hk
      by_cases hq : (q == k) = true <;> simp [assocLookupSkel, hq]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, assocLookupSkel]
      by_cases hqh : (q == kh) = true
      · have hqk : (q == k) = false := by
          have heq1 := eq_of_beq hqh; subst heq1
          cases h2 : (q == k)
          · rfl
          · have heq2 := eq_of_beq h2; subst heq2; simp at h
        simp [hqh, hqk]
      · simp [hqh, assocLookupSkel_assocSetSkel q k v tl]

mutual
  /-- Skeleton-guided value relation between two `TomlValue` nodes. -/
  def SkelNodeRel : SkeletonNode → TomlValue → TomlValue → Prop
    | .leaf, v1, v2 => TomlEquiv v1 v2
    | .inlineTable, v1, v2 => TomlEquiv v1 v2
    | .table _ subSkel, .table sub1, .table sub2 => SkelRel subSkel sub1.toList sub2.toList
    | .table _ _, _, _ => True
    | .aot elems, .array xs1, .array xs2 => SkelAotRel elems xs1.toList xs2.toList
    | .aot _, _, _ => True
  termination_by sn _ _ => sizeOf sn * 2
  decreasing_by all_goals simp +arith

  /-- Skeleton-guided agreement invariant between two table association lists `e1` and `e2`. -/
  def SkelRel (skel : List (String × SkeletonNode))
      (e1 e2 : List (String × TomlValue)) : Prop :=
    ∀ k sn, assocLookupSkel k skel = some sn →
      match lookupKeyList k e1, lookupKeyList k e2 with
      | some v1, some v2 => SkelNodeRel sn v1 v2
      | _, _ => sn ≠ .leaf ∧ sn ≠ .inlineTable
  termination_by sizeOf skel * 2 + 1
  decreasing_by
    have hlt := assocLookupSkel_sizeOf_lt skel ‹_›
    omega

  /-- Element-wise `SkelRel` across an `[[aot]]` skeleton list and two `TomlValue` lists. -/
  def SkelAotRel : List (List (String × SkeletonNode)) → List TomlValue → List TomlValue → Prop
    | [], _, _ => True
    | eSkel :: restSkel, .table d1 :: rest1, .table d2 :: rest2 =>
      SkelRel eSkel d1.toList d2.toList ∧ SkelAotRel restSkel rest1 rest2
    | _ :: restSkel, _ :: rest1, _ :: rest2 => SkelAotRel restSkel rest1 rest2
    | _, _, _ => True
  termination_by elems _ _ => sizeOf elems * 2
  decreasing_by all_goals simp +arith
end

theorem SkelRel.lookup {skel : List (String × SkeletonNode)} {e1 e2 : List (String × TomlValue)}
    (h : SkelRel skel e1 e2) (k : String) (sn : SkeletonNode) (hlu : assocLookupSkel k skel = some sn) :
    match lookupKeyList k e1, lookupKeyList k e2 with
    | some v1, some v2 => SkelNodeRel sn v1 v2
    | _, _ => sn ≠ .leaf ∧ sn ≠ .inlineTable := by
  rw [SkelRel] at h
  exact h k sn hlu

theorem skelRel_nil (e1 e2 : List (String × TomlValue)) : SkelRel [] e1 e2 := by
  rw [SkelRel]; intro _ _ h; nomatch h

theorem skelRel_assocSet {k : String} {sn : SkeletonNode}
    {skel : List (String × SkeletonNode)} {e1 e2 : List (String × TomlValue)}
    (hrel : SkelRel skel e1 e2)
    (hnew : match lookupKeyList k e1, lookupKeyList k e2 with
      | some v1, some v2 => SkelNodeRel sn v1 v2
      | _, _ => sn ≠ .leaf ∧ sn ≠ .inlineTable) :
    SkelRel (assocSetSkel k sn skel) e1 e2 := by
  rw [SkelRel]
  intro q sq hlu
  rw [assocLookupSkel_assocSetSkel] at hlu
  by_cases hqk : (q == k) = true
  · rw [hqk] at hlu; simp only [↓reduceIte, Option.some.injEq] at hlu
    have hqe := eq_of_beq hqk; subst hqe sq; exact hnew
  · simp only [hqk, Bool.false_eq_true, ↓reduceIte] at hlu
    exact hrel.lookup q sq hlu

private theorem skelAotRel_append_empty :
    ∀ (elems : List (List (String × SkeletonNode))) (xs1 xs2 : List TomlValue),
      SkelAotRel elems xs1 xs2 → SkelAotRel (elems ++ [[]]) xs1 xs2
  | [], xs1, xs2, _ => by
    cases xs1 with
    | nil => simp [SkelAotRel]
    | cons x1 r1 =>
      cases xs2 with
      | nil => simp [SkelAotRel]
      | cons x2 r2 =>
        cases x1 <;> cases x2 <;> simp [SkelAotRel, skelRel_nil]
  | e :: es, xs1, xs2, h => by
    cases xs1 with
    | nil => simp [SkelAotRel]
    | cons x1 r1 =>
      cases xs2 with
      | nil => simp [SkelAotRel]
      | cons x2 r2 =>
        cases x1 with
        | table d1 =>
          cases x2 with
          | table d2 =>
            simp only [List.cons_append, SkelAotRel] at h ⊢
            exact ⟨h.1, skelAotRel_append_empty es r1 r2 h.2⟩
          | _ => simp only [List.cons_append, SkelAotRel] at h ⊢; exact skelAotRel_append_empty es r1 r2 h
        | _ =>
          cases x2 <;> (simp only [List.cons_append, SkelAotRel] at h ⊢; exact skelAotRel_append_empty es r1 r2 h)

private theorem skelAotWF_append_empty :
    ∀ (elems : List (List (String × SkeletonNode))),
      skelAotWF elems = true → skelAotWF (elems ++ [[]]) = true
  | [], _ => by simp [skelAotWF, skelEntriesWF]
  | e :: es, h => by
    have hp : skelEntriesWF e = true ∧ skelAotWF es = true := by simpa [skelAotWF, Bool.and_eq_true] using h
    simp [List.cons_append, skelAotWF, hp.1, skelAotWF_append_empty es hp.2]

private theorem mapLastSkelAot_preserves (f : List (String × SkeletonNode) → Option (List (String × SkeletonNode)))
    (hf : ∀ s s', skelEntriesWF s = true → f s = some s' →
      skelEntriesWF s' = true ∧ ∀ d1 d2, SkelRel s d1 d2 → SkelRel s' d1 d2) :
    ∀ (elems nextElems : List (List (String × SkeletonNode))),
      skelAotWF elems = true → mapLastSkelAot f elems = some nextElems →
      skelAotWF nextElems = true ∧ ∀ xs1 xs2, SkelAotRel elems xs1 xs2 → SkelAotRel nextElems xs1 xs2
  | [], _, _, h => by simp [mapLastSkelAot] at h
  | [last], nextElems, hwf, hm => by
    have hwf_last : skelEntriesWF last = true := by simpa [skelAotWF] using hwf
    simp only [mapLastSkelAot, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hm
    rcases hm with ⟨upd, hupd, rfl⟩
    obtain ⟨hwf', hrel'⟩ := hf last upd hwf_last hupd
    refine ⟨by simp [skelAotWF, hwf'], fun xs1 xs2 ha => ?_⟩
    cases xs1 with
    | nil => simp [SkelAotRel]
    | cons x1 r1 =>
      cases xs2 with
      | nil => simp [SkelAotRel]
      | cons x2 r2 =>
        cases x1 with
        | table d1 =>
          cases x2 with
          | table d2 => simp only [SkelAotRel] at ha ⊢; exact ⟨hrel' _ _ ha.1, trivial⟩
          | _ => simp [SkelAotRel]
        | _ => cases x2 <;> simp [SkelAotRel]
  | hd :: nxt :: tl, nextElems, hwf, hm => by
    have hwf_p : skelEntriesWF hd = true ∧ skelAotWF (nxt :: tl) = true := by
      simpa [skelAotWF, Bool.and_eq_true] using hwf
    simp only [mapLastSkelAot, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hm
    rcases hm with ⟨rest', hrest, rfl⟩
    obtain ⟨hwf_r, hrel_r⟩ := mapLastSkelAot_preserves f hf (nxt :: tl) rest' hwf_p.2 hrest
    refine ⟨by simp [skelAotWF, hwf_p.1, hwf_r], fun xs1 xs2 ha => ?_⟩
    cases xs1 with
    | nil => simp [SkelAotRel]
    | cons x1 r1 =>
      cases xs2 with
      | nil => simp [SkelAotRel]
      | cons x2 r2 =>
        cases x1 with
        | table d1 =>
          cases x2 with
          | table d2 => simp only [SkelAotRel] at ha ⊢; exact ⟨ha.1, hrel_r r1 r2 ha.2⟩
          | _ => simp only [SkelAotRel] at ha ⊢; exact hrel_r r1 r2 ha
        | _ => cases x2 <;> (simp only [SkelAotRel] at ha ⊢; exact hrel_r r1 r2 ha)

private theorem table_ne_leaf_inline {k : OpenTableKind} {s : List (String × SkeletonNode)} :
    SkeletonNode.table k s ≠ .leaf ∧ SkeletonNode.table k s ≠ .inlineTable :=
  ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

private theorem aot_ne_leaf_inline {es : List (List (String × SkeletonNode))} :
    SkeletonNode.aot es ≠ .leaf ∧ SkeletonNode.aot es ≠ .inlineTable :=
  ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- `applyHeaderSkel` preserves `skelEntriesWF` and `SkelRel` across any `e1, e2`. -/
theorem applyHeaderSkel_preserves (isAot : Bool) :
    ∀ (path : List String) (skel nextSkel : List (String × SkeletonNode)),
      skelEntriesWF skel = true → applyHeaderSkel isAot skel path = some nextSkel →
      skelEntriesWF nextSkel = true ∧ ∀ e1 e2, SkelRel skel e1 e2 → SkelRel nextSkel e1 e2
  | [], _, _, _, h => by simp [applyHeaderSkel] at h
  | [k], skel, nextSkel, hwf, h => by
    simp only [applyHeaderSkel, applyHeaderLeafSkel] at h
    cases isAot with
    | false =>
      cases hlu : assocLookupSkel k skel with
      | none =>
        rw [hlu] at h; injection h with heq; subst heq
        refine ⟨skelEntriesWF_assocSetSkel hwf (by simp [skelNodeWF, skelEntriesWF]), fun e1 e2 hrel => skelRel_assocSet hrel ?_⟩
        cases lookupKeyList k e1 with
        | none => exact table_ne_leaf_inline
        | some v1 =>
          cases lookupKeyList k e2 with
          | none => exact table_ne_leaf_inline
          | some v2 => cases v1 <;> cases v2 <;> simp [SkelNodeRel, skelRel_nil]
      | some sn =>
        rw [hlu] at h
        cases sn with
        | table kind sub =>
          cases kind with
          | subtableImplicit =>
            injection h with heq; subst heq
            have hsn_wf : skelNodeWF (.table .explicit sub) = true := by
              have hw := assocLookupSkel_wf hwf hlu; simpa [skelNodeWF] using hw
            refine ⟨skelEntriesWF_assocSetSkel hwf hsn_wf, fun e1 e2 hrel => skelRel_assocSet hrel ?_⟩
            have hprev := hrel.lookup k (.table .subtableImplicit sub) hlu
            cases hk1 : lookupKeyList k e1 with
            | none => exact table_ne_leaf_inline
            | some v1 =>
              cases hk2 : lookupKeyList k e2 with
              | none => exact table_ne_leaf_inline
              | some v2 =>
                rw [hk1, hk2] at hprev
                cases v1 <;> cases v2 <;> first | (simp [SkelNodeRel]; done) | (simpa [SkelNodeRel] using hprev)
          | _ => simp at h
        | _ => simp at h
    | true =>
      cases hlu : assocLookupSkel k skel with
      | none =>
        rw [hlu] at h; injection h with heq; subst heq
        refine ⟨skelEntriesWF_assocSetSkel hwf (by simp [skelNodeWF, skelAotWF, skelEntriesWF]),
          fun e1 e2 hrel => skelRel_assocSet hrel ?_⟩
        cases lookupKeyList k e1 with
        | none => exact aot_ne_leaf_inline
        | some v1 =>
          cases lookupKeyList k e2 with
          | none => exact aot_ne_leaf_inline
          | some v2 =>
            cases v1 with
            | array xs1 =>
              cases v2 with
              | array xs2 =>
                simp only [SkelNodeRel]
                exact skelAotRel_append_empty [] xs1.toList xs2.toList (by simp [SkelAotRel])
              | _ => simp [SkelNodeRel]
            | _ => cases v2 <;> simp [SkelNodeRel]
      | some sn =>
        rw [hlu] at h
        cases sn with
        | aot elems =>
          injection h with heq; subst heq
          have he_wf : skelAotWF elems = true := by simpa [skelNodeWF] using assocLookupSkel_wf hwf hlu
          refine ⟨skelEntriesWF_assocSetSkel hwf (by simpa [skelNodeWF] using skelAotWF_append_empty elems he_wf),
            fun e1 e2 hrel => skelRel_assocSet hrel ?_⟩
          have hprev := hrel.lookup k (.aot elems) hlu
          cases hk1 : lookupKeyList k e1 with
          | none => exact aot_ne_leaf_inline
          | some v1 =>
            cases hk2 : lookupKeyList k e2 with
            | none => exact aot_ne_leaf_inline
            | some v2 =>
              rw [hk1, hk2] at hprev
              cases v1 with
              | array xs1 =>
                cases v2 with
                | array xs2 =>
                  simp only [SkelNodeRel] at hprev ⊢
                  exact skelAotRel_append_empty elems xs1.toList xs2.toList hprev
                | _ => simp [SkelNodeRel]
              | _ => cases v2 <;> simp [SkelNodeRel]
        | _ => simp at h
  | k :: k' :: rest, skel, nextSkel, hwf, h => by
    simp only [applyHeaderSkel] at h
    cases hlu : assocLookupSkel k skel with
    | none =>
      rw [hlu] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      rcases h with ⟨sub, hsub, rfl⟩
      obtain ⟨hsub_wf, hsub_rel⟩ := applyHeaderSkel_preserves isAot (k' :: rest) [] sub (by simp [skelEntriesWF]) hsub
      refine ⟨skelEntriesWF_assocSetSkel hwf (by simpa [skelNodeWF] using hsub_wf),
        fun e1 e2 hrel => skelRel_assocSet hrel ?_⟩
      cases lookupKeyList k e1 with
      | none => exact table_ne_leaf_inline
      | some v1 =>
        cases lookupKeyList k e2 with
        | none => exact table_ne_leaf_inline
        | some v2 =>
          cases v1 with
          | table d1 =>
            cases v2 with
            | table d2 => simp only [SkelNodeRel]; exact hsub_rel _ _ (skelRel_nil _ _)
            | _ => simp [SkelNodeRel]
          | _ => cases v2 <;> simp [SkelNodeRel]
    | some sn =>
      rw [hlu] at h
      cases sn with
      | table kind sub =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        rcases h with ⟨nextSub, hsub, rfl⟩
        have hsub_wf0 : skelEntriesWF sub = true := by simpa [skelNodeWF] using assocLookupSkel_wf hwf hlu
        obtain ⟨hsub_wf, hsub_rel⟩ := applyHeaderSkel_preserves isAot (k' :: rest) sub nextSub hsub_wf0 hsub
        refine ⟨skelEntriesWF_assocSetSkel hwf (by simpa [skelNodeWF] using hsub_wf),
          fun e1 e2 hrel => skelRel_assocSet hrel ?_⟩
        have hprev := hrel.lookup k (.table kind sub) hlu
        cases hk1 : lookupKeyList k e1 with
        | none => exact table_ne_leaf_inline
        | some v1 =>
          cases hk2 : lookupKeyList k e2 with
          | none => exact table_ne_leaf_inline
          | some v2 =>
            rw [hk1, hk2] at hprev
            cases v1 with
            | table d1 =>
              cases v2 with
              | table d2 => simp only [SkelNodeRel] at hprev ⊢; exact hsub_rel _ _ hprev
              | _ => simp [SkelNodeRel]
            | _ => cases v2 <;> simp [SkelNodeRel]
      | aot elems =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        rcases h with ⟨nextElems, helems, rfl⟩
        have helems_wf0 : skelAotWF elems = true := by simpa [skelNodeWF] using assocLookupSkel_wf hwf hlu
        obtain ⟨helems_wf, helems_rel⟩ := mapLastSkelAot_preserves
          (fun elem => applyHeaderSkel isAot elem (k' :: rest))
          (fun s s' hs hf => applyHeaderSkel_preserves isAot (k' :: rest) s s' hs hf)
          elems nextElems helems_wf0 helems
        refine ⟨skelEntriesWF_assocSetSkel hwf (by simpa [skelNodeWF] using helems_wf),
          fun e1 e2 hrel => skelRel_assocSet hrel ?_⟩
        have hprev := hrel.lookup k (.aot elems) hlu
        cases hk1 : lookupKeyList k e1 with
        | none => exact aot_ne_leaf_inline
        | some v1 =>
          cases hk2 : lookupKeyList k e2 with
          | none => exact aot_ne_leaf_inline
          | some v2 =>
            rw [hk1, hk2] at hprev
            cases v1 with
            | array xs1 =>
              cases v2 with
              | array xs2 => simp only [SkelNodeRel] at hprev ⊢; exact helems_rel _ _ hprev
              | _ => simp [SkelNodeRel]
            | _ => cases v2 <;> simp [SkelNodeRel]
      | _ => simp at h

end LeanSwe.Toml.Proofs

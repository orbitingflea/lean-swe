import LeanSweProofs.Toml.Proofs.RenderInjectiveSkel

/-!
# Active-Path Insertion Determinism & Final `TomlTableEquiv` Extraction

Completes the skeleton-guided determinism and equivalence lemmas for `insertDottedAndLookup`,
`insertAtActiveAndLookup`, and `skelMatchesEntries` without importing `Toml.Impl`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model

private def skelTagOf : TomlValue → SkeletonNode
  | .table _ => .inlineTable
  | _ => .leaf

private theorem skelTagOf_eq_of_tomlEquiv {v1 v2 : TomlValue} (heq : TomlEquiv v1 v2) :
    skelTagOf v1 = skelTagOf v2 := by
  cases v1 <;> cases v2 <;> first | rfl | (simp [TomlEquiv] at heq)

/-- `insertDottedAndLookup` produces identical updated skeletons and preserves `SkelRel` when target values satisfy `TomlEquiv`. -/
theorem insertDottedAndLookup_rel :
    ∀ (relPath : List String) (skel s1 s2 : List (String × SkeletonNode))
      (e1 e2 : List (String × TomlValue)) (v1 v2 : TomlValue),
      SkelRel skel e1 e2 →
      insertDottedAndLookup e1 skel relPath = some (s1, v1) →
      insertDottedAndLookup e2 skel relPath = some (s2, v2) →
      TomlEquiv v1 v2 →
      s1 = s2 ∧ SkelRel s1 e1 e2
  | [], _, _, _, _, _, _, _, _, h1, _, _ => by simp [insertDottedAndLookup] at h1
  | [k], skel, s1, s2, e1, e2, v1, v2, hrel, h1, h2, heqv => by
    simp only [insertDottedAndLookup] at h1 h2
    cases hlu : assocLookupSkel k skel with
    | some _ => simp [hlu] at h1
    | none =>
      rw [hlu] at h1 h2
      cases hk1 : lookupKeyList k e1 with
      | none => simp [hk1] at h1
      | some w1 =>
        rw [hk1] at h1
        cases hk2 : lookupKeyList k e2 with
        | none => simp [hk2] at h2
        | some w2 =>
          rw [hk2] at h2
          simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
          rcases h1 with ⟨rfl, rfl⟩
          rcases h2 with ⟨rfl, rfl⟩
          change assocSetSkel k (skelTagOf w1) skel = assocSetSkel k (skelTagOf w2) skel ∧
            SkelRel (assocSetSkel k (skelTagOf w1) skel) e1 e2
          rw [← skelTagOf_eq_of_tomlEquiv heqv]
          refine ⟨rfl, skelRel_assocSet hrel ?_⟩
          rw [hk1, hk2]
          cases w1 <;> simp [skelTagOf, SkelNodeRel, heqv]
  | k :: k' :: rest, skel, s1, s2, e1, e2, v1, v2, hrel, h1, h2, heqv => by
    simp only [insertDottedAndLookup] at h1 h2
    cases hk1 : lookupKeyList k e1 with
    | none => simp [hk1] at h1
    | some w1 =>
      rw [hk1] at h1
      cases w1 with
      | table sub1 =>
        cases hk2 : lookupKeyList k e2 with
        | none => simp [hk2] at h2
        | some w2 =>
          rw [hk2] at h2
          cases w2 with
          | table sub2 =>
            cases hlu : assocLookupSkel k skel with
            | none =>
              rw [hlu] at h1 h2
              simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h1 h2
              rcases h1 with ⟨⟨ns1, u1⟩, hi1, ⟨rfl, rfl⟩⟩
              rcases h2 with ⟨⟨ns2, u2⟩, hi2, ⟨rfl, rfl⟩⟩
              obtain ⟨rfl, hns_rel⟩ := insertDottedAndLookup_rel (k' :: rest) [] ns1 ns2
                sub1.toList sub2.toList u1 u2 (skelRel_nil _ _) hi1 hi2 heqv
              refine ⟨rfl, skelRel_assocSet hrel ?_⟩
              rw [hk1, hk2]; simp only [SkelNodeRel]; exact hns_rel
            | some sn =>
              rw [hlu] at h1 h2
              have hprev := hrel.lookup k sn hlu
              rw [hk1, hk2] at hprev
              cases sn with
              | table kind subSkel =>
                simp only [SkelNodeRel] at hprev
                cases kind with
                | subtableImplicit | dotted =>
                  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h1 h2
                  rcases h1 with ⟨⟨ns1, u1⟩, hi1, ⟨rfl, rfl⟩⟩
                  rcases h2 with ⟨⟨ns2, u2⟩, hi2, ⟨rfl, rfl⟩⟩
                  obtain ⟨rfl, hns_rel⟩ := insertDottedAndLookup_rel (k' :: rest) subSkel ns1 ns2
                    sub1.toList sub2.toList u1 u2 hprev hi1 hi2 heqv
                  refine ⟨rfl, skelRel_assocSet hrel ?_⟩
                  rw [hk1, hk2]; simp only [SkelNodeRel]; exact hns_rel
                | explicit => simp at h1
              | leaf | inlineTable | aot _ => simp at h1
          | _ => simp at h2
      | _ => simp at h1

private theorem mapLastSkelWithDoc_rel
    (f : List (String × TomlValue) → List (String × SkeletonNode) →
      Option (List (String × SkeletonNode) × TomlValue))
    (hf : ∀ d1 d2 s s1 s2 u1 u2, SkelRel s d1 d2 →
      f d1 s = some (s1, u1) → f d2 s = some (s2, u2) → TomlEquiv u1 u2 → s1 = s2 ∧ SkelRel s1 d1 d2) :
    ∀ (elems ne1 ne2 : List (List (String × SkeletonNode)))
      (xs1 xs2 : List TomlValue) (v1 v2 : TomlValue),
      SkelAotRel elems xs1 xs2 →
      mapLastSkelWithDoc f xs1 elems = some (ne1, v1) →
      mapLastSkelWithDoc f xs2 elems = some (ne2, v2) →
      TomlEquiv v1 v2 →
      ne1 = ne2 ∧ SkelAotRel ne1 xs1 xs2
  | [], _, _, _, _, _, _, _, h1, _, _ => by simp [mapLastSkelWithDoc] at h1
  | [last], ne1, ne2, xs1, xs2, v1, v2, ha, h1, h2, heqv => by
    cases xs1 with
    | nil => simp [mapLastSkelWithDoc] at h1
    | cons x1 r1 =>
      cases x1 with
      | table d1 =>
        cases xs2 with
        | nil => simp [mapLastSkelWithDoc] at h2
        | cons x2 r2 =>
          cases x2 with
          | table d2 =>
            simp only [SkelAotRel] at ha
            simp only [mapLastSkelWithDoc, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h1 h2
            rcases h1 with ⟨⟨u1, w1⟩, hf1, ⟨rfl, rfl⟩⟩
            rcases h2 with ⟨⟨u2, w2⟩, hf2, ⟨rfl, rfl⟩⟩
            obtain ⟨rfl, hrel'⟩ := hf d1.toList d2.toList last u1 u2 w1 w2 ha.1 hf1 hf2 heqv
            refine ⟨rfl, ?_⟩
            unfold SkelAotRel
            exact ⟨hrel', by simp [SkelAotRel]⟩
          | _ => simp [mapLastSkelWithDoc] at h2
      | _ => simp [mapLastSkelWithDoc] at h1
  | hd :: nxt :: tl, ne1, ne2, xs1, xs2, v1, v2, ha, h1, h2, heqv => by
    cases xs1 with
    | nil => simp [mapLastSkelWithDoc] at h1
    | cons x1 r1 =>
      cases x1 with
      | table d1 =>
        cases xs2 with
        | nil => simp [mapLastSkelWithDoc] at h2
        | cons x2 r2 =>
          cases x2 with
          | table d2 =>
            simp only [SkelAotRel] at ha
            simp only [mapLastSkelWithDoc, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h1 h2
            rcases h1 with ⟨⟨ru1, w1⟩, hr1, ⟨rfl, rfl⟩⟩
            rcases h2 with ⟨⟨ru2, w2⟩, hr2, ⟨rfl, rfl⟩⟩
            obtain ⟨rfl, hrel_r⟩ := mapLastSkelWithDoc_rel f hf (nxt :: tl) ru1 ru2 r1 r2 w1 w2 ha.2 hr1 hr2 heqv
            refine ⟨rfl, ?_⟩
            unfold SkelAotRel
            exact ⟨ha.1, hrel_r⟩
          | _ => simp [mapLastSkelWithDoc] at h2
      | _ => simp [mapLastSkelWithDoc] at h1

/-- `insertAtActiveAndLookup` produces identical updated skeletons and preserves `SkelRel` when target values satisfy `TomlEquiv`. -/
theorem insertAtActiveAndLookup_rel :
    ∀ (activePath : List String) (relPath : List String)
      (skel s1 s2 : List (String × SkeletonNode))
      (e1 e2 : List (String × TomlValue)) (v1 v2 : TomlValue),
      SkelRel skel e1 e2 →
      insertAtActiveAndLookup e1 skel activePath relPath = some (s1, v1) →
      insertAtActiveAndLookup e2 skel activePath relPath = some (s2, v2) →
      TomlEquiv v1 v2 →
      s1 = s2 ∧ SkelRel s1 e1 e2
  | [], relPath, skel, s1, s2, e1, e2, v1, v2, hrel, h1, h2, heqv =>
    insertDottedAndLookup_rel relPath skel s1 s2 e1 e2 v1 v2 hrel h1 h2 heqv
  | k :: rest, relPath, skel, s1, s2, e1, e2, v1, v2, hrel, h1, h2, heqv => by
    simp only [insertAtActiveAndLookup] at h1 h2
    cases hlu : assocLookupSkel k skel with
    | none => simp [hlu] at h1
    | some sn =>
      rw [hlu] at h1 h2
      have hprev := hrel.lookup k sn hlu
      cases sn with
      | table kind subSkel =>
        cases hk1 : lookupKeyList k e1 with
        | none => simp [hk1] at h1
        | some w1 =>
          rw [hk1] at h1 hprev
          cases w1 with
          | table sub1 =>
            cases hk2 : lookupKeyList k e2 with
            | none => simp [hk2] at h2
            | some w2 =>
              rw [hk2] at h2 hprev
              cases w2 with
              | table sub2 =>
                simp only [SkelNodeRel] at hprev
                simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h1 h2
                rcases h1 with ⟨⟨ns1, u1⟩, hi1, ⟨rfl, rfl⟩⟩
                rcases h2 with ⟨⟨ns2, u2⟩, hi2, ⟨rfl, rfl⟩⟩
                obtain ⟨rfl, hns_rel⟩ := insertAtActiveAndLookup_rel rest relPath subSkel ns1 ns2
                  sub1.toList sub2.toList u1 u2 hprev hi1 hi2 heqv
                refine ⟨rfl, skelRel_assocSet hrel ?_⟩
                rw [hk1, hk2]; simp only [SkelNodeRel]; exact hns_rel
              | _ => simp at h2
          | _ => simp at h1
      | aot elems =>
        cases hk1 : lookupKeyList k e1 with
        | none => simp [hk1] at h1
        | some w1 =>
          rw [hk1] at h1 hprev
          cases w1 with
          | array xs1 =>
            cases hk2 : lookupKeyList k e2 with
            | none => simp [hk2] at h2
            | some w2 =>
              rw [hk2] at h2 hprev
              cases w2 with
              | array xs2 =>
                simp only [SkelNodeRel] at hprev
                simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h1 h2
                rcases h1 with ⟨⟨ne1, u1⟩, hm1, ⟨rfl, rfl⟩⟩
                rcases h2 with ⟨⟨ne2, u2⟩, hm2, ⟨rfl, rfl⟩⟩
                obtain ⟨rfl, hne_rel⟩ := mapLastSkelWithDoc_rel
                  (fun ed es => insertAtActiveAndLookup ed es rest relPath)
                  (fun d1 d2 s ns1 ns2 z1 z2 hr f1 f2 hz =>
                    insertAtActiveAndLookup_rel rest relPath s ns1 ns2 d1 d2 z1 z2 hr f1 f2 hz)
                  elems ne1 ne2 xs1.toList xs2.toList u1 u2 hprev hm1 hm2 heqv
                refine ⟨rfl, skelRel_assocSet hrel ?_⟩
                rw [hk1, hk2]; simp only [SkelNodeRel]; exact hne_rel
              | _ => simp at h2
          | _ => simp at h1
      | leaf | inlineTable =>
        cases lookupKeyList k e1 <;> simp at h1

private theorem lookupKeyList_mem_fst {k : String} {v : TomlValue} :
    ∀ es : List (String × TomlValue), lookupKeyList k es = some v → ∃ p ∈ es, p.1 = k
  | [], h => nomatch h
  | (k', v') :: rest, h => by
    simp only [lookupKeyList] at h
    by_cases hk : (k == k') = true
    · exact ⟨(k', v'), List.mem_cons_self, (eq_of_beq hk).symm⟩
    · simp only [hk, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨p, hp, hpk⟩ := lookupKeyList_mem_fst rest h
      exact ⟨p, List.mem_cons_of_mem _ hp, hpk⟩

/-- `insertDottedAndLookup` preserves `skelEntriesWF`. -/
theorem insertDottedAndLookup_wf :
    ∀ (relPath : List String) (skel s : List (String × SkeletonNode))
      (e : List (String × TomlValue)) (v : TomlValue),
      skelEntriesWF skel = true →
      insertDottedAndLookup e skel relPath = some (s, v) →
      skelEntriesWF s = true
  | [], _, _, _, _, _, h => by simp [insertDottedAndLookup] at h
  | [k], skel, s, e, v, hwf, h => by
    simp only [insertDottedAndLookup] at h
    cases hlu : assocLookupSkel k skel with
    | some _ => simp [hlu] at h
    | none =>
      rw [hlu] at h
      cases hk : lookupKeyList k e with
      | none => simp [hk] at h
      | some w =>
        rw [hk] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact skelEntriesWF_assocSetSkel hwf (by cases w <;> simp [skelNodeWF])
  | k :: k' :: rest, skel, s, e, v, hwf, h => by
    simp only [insertDottedAndLookup] at h
    cases hk : lookupKeyList k e with
    | none => simp [hk] at h
    | some w =>
      rw [hk] at h
      cases w with
      | table sub =>
        cases hlu : assocLookupSkel k skel with
        | none =>
          rw [hlu] at h
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨⟨ns, u⟩, hi, ⟨rfl, rfl⟩⟩
          exact skelEntriesWF_assocSetSkel hwf
            (by simpa [skelNodeWF] using insertDottedAndLookup_wf (k' :: rest) [] ns sub.toList u (by simp [skelEntriesWF]) hi)
        | some sn =>
          rw [hlu] at h
          have hsn := assocLookupSkel_wf hwf hlu
          cases sn with
          | table kind subSkel =>
            have hsub_wf : skelEntriesWF subSkel = true := by simpa [skelNodeWF] using hsn
            cases kind with
            | subtableImplicit | dotted =>
              simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨⟨ns, u⟩, hi, ⟨rfl, rfl⟩⟩
              exact skelEntriesWF_assocSetSkel hwf
                (by simpa [skelNodeWF] using insertDottedAndLookup_wf (k' :: rest) subSkel ns sub.toList u hsub_wf hi)
            | explicit => simp at h
          | leaf | inlineTable | aot _ => simp at h
      | _ => simp at h

private theorem mapLastSkelWithDoc_wf
    (f : List (String × TomlValue) → List (String × SkeletonNode) →
      Option (List (String × SkeletonNode) × TomlValue))
    (hf : ∀ d s s' u, skelEntriesWF s = true → f d s = some (s', u) → skelEntriesWF s' = true) :
    ∀ (elems ne : List (List (String × SkeletonNode))) (xs : List TomlValue) (v : TomlValue),
      skelAotWF elems = true →
      mapLastSkelWithDoc f xs elems = some (ne, v) →
      skelAotWF ne = true
  | [], _, _, _, _, h => by simp [mapLastSkelWithDoc] at h
  | [last], ne, xs, v, hwf, h => by
    cases xs with
    | nil => simp [mapLastSkelWithDoc] at h
    | cons x r =>
      cases x with
      | table d =>
        have hwf_l : skelEntriesWF last = true := by simpa [skelAotWF] using hwf
        simp only [mapLastSkelWithDoc, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨⟨u, w⟩, hfu, ⟨rfl, rfl⟩⟩
        simp [skelAotWF, hf d.toList last u w hwf_l hfu]
      | _ => simp [mapLastSkelWithDoc] at h
  | hd :: nxt :: tl, ne, xs, v, hwf, h => by
    cases xs with
    | nil => simp [mapLastSkelWithDoc] at h
    | cons x r =>
      cases x with
      | table d =>
        have hwf_p : skelEntriesWF hd = true ∧ skelAotWF (nxt :: tl) = true := by
          simpa [skelAotWF, Bool.and_eq_true] using hwf
        simp only [mapLastSkelWithDoc, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨⟨ru, w⟩, hru, ⟨rfl, rfl⟩⟩
        simp [skelAotWF, hwf_p.1, mapLastSkelWithDoc_wf f hf (nxt :: tl) ru r w hwf_p.2 hru]
      | _ => simp [mapLastSkelWithDoc] at h

/-- `insertAtActiveAndLookup` preserves `skelEntriesWF`. -/
theorem insertAtActiveAndLookup_wf :
    ∀ (activePath relPath : List String) (skel s : List (String × SkeletonNode))
      (e : List (String × TomlValue)) (v : TomlValue),
      skelEntriesWF skel = true →
      insertAtActiveAndLookup e skel activePath relPath = some (s, v) →
      skelEntriesWF s = true
  | [], relPath, skel, s, e, v, hwf, h => insertDottedAndLookup_wf relPath skel s e v hwf h
  | k :: rest, relPath, skel, s, e, v, hwf, h => by
    simp only [insertAtActiveAndLookup] at h
    cases hlu : assocLookupSkel k skel with
    | none => simp [hlu] at h
    | some sn =>
      rw [hlu] at h
      have hsn := assocLookupSkel_wf hwf hlu
      cases sn with
      | table kind subSkel =>
        have hsub_wf : skelEntriesWF subSkel = true := by simpa [skelNodeWF] using hsn
        cases hk : lookupKeyList k e with
        | none => simp [hk] at h
        | some w =>
          rw [hk] at h
          cases w with
          | table sub =>
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨⟨ns, u⟩, hi, ⟨rfl, rfl⟩⟩
            exact skelEntriesWF_assocSetSkel hwf
              (by simpa [skelNodeWF] using insertAtActiveAndLookup_wf rest relPath subSkel ns sub.toList u hsub_wf hi)
          | _ => simp at h
      | aot elems =>
        have helems_wf : skelAotWF elems = true := by simpa [skelNodeWF] using hsn
        cases hk : lookupKeyList k e with
        | none => simp [hk] at h
        | some w =>
          rw [hk] at h
          cases w with
          | array xs =>
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨⟨ne, u⟩, hm, ⟨rfl, rfl⟩⟩
            have hne_wf := mapLastSkelWithDoc_wf
              (fun ed es => insertAtActiveAndLookup ed es rest relPath)
              (fun d es es' z hs hf => insertAtActiveAndLookup_wf rest relPath es es' d z hs hf)
              elems ne xs.toList u helems_wf hm
            exact skelEntriesWF_assocSetSkel hwf (by simpa [skelNodeWF] using hne_wf)
          | _ => simp at h
      | leaf | inlineTable =>
        cases lookupKeyList k e <;> simp at h

private theorem skelMatchesEntriesAll_lookup {k : String} {sn : SkeletonNode} {es : List (String × TomlValue)} :
    ∀ skel : List (String × SkeletonNode),
      skelMatchesEntriesAll skel es = true → assocLookupSkel k skel = some sn →
      ∃ v, lookupKeyList k es = some v ∧ skelNodeMatchesValue sn v = true
  | [], _, hlu => nomatch hlu
  | (k', sn') :: rest, hall, hlu => by
    simp only [skelMatchesEntriesAll, Bool.and_eq_true] at hall
    simp only [assocLookupSkel] at hlu
    by_cases hk : (k == k') = true
    · rw [hk] at hlu; simp only [↓reduceIte, Option.some.injEq] at hlu
      have heq := eq_of_beq hk; subst heq hlu
      cases hlk : lookupKeyList k es with
      | none => simp [hlk] at hall
      | some v => rw [hlk] at hall; exact ⟨v, rfl, hall.1⟩
    · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hlu
      exact skelMatchesEntriesAll_lookup rest hall.2 hlu

mutual
  /-- Convert matching `SkeletonNode` coverage + `SkelNodeRel` into `TomlEquiv`. -/
  theorem skelNodeMatches_equiv :
      ∀ (sn : SkeletonNode) (v1 v2 : TomlValue),
        skelNodeMatchesValue sn v1 = true → skelNodeMatchesValue sn v2 = true →
        SkelNodeRel sn v1 v2 → TomlEquiv v1 v2
    | .leaf, v1, v2, _, _, hrel => by simpa [SkelNodeRel] using hrel
    | .inlineTable, v1, v2, _, _, hrel => by simpa [SkelNodeRel] using hrel
    | .table _ subSkel, v1, v2, hm1, hm2, hrel => by
      cases v1 with
      | table sub1 =>
        cases v2 with
        | table sub2 =>
          simp only [skelNodeMatchesValue] at hm1 hm2
          simp only [SkelNodeRel] at hrel
          unfold TomlEquiv
          exact skelMatchesEntries_equiv subSkel sub1.toList sub2.toList hm1 hm2 hrel
        | _ => simp [skelNodeMatchesValue] at hm2
      | _ => simp [skelNodeMatchesValue] at hm1
    | .aot elems, v1, v2, hm1, hm2, hrel => by
      cases v1 with
      | array xs1 =>
        cases v2 with
        | array xs2 =>
          simp only [skelNodeMatchesValue] at hm1 hm2
          simp only [SkelNodeRel] at hrel
          unfold TomlEquiv
          exact skelMatchesAot_equiv elems xs1.toList xs2.toList hm1 hm2 hrel
        | _ => simp [skelNodeMatchesValue] at hm2
      | _ => simp [skelNodeMatchesValue] at hm1
  termination_by sn _ _ => sizeOf sn * 2
  decreasing_by all_goals simp +arith

  /-- Convert bidirectional `skelMatchesEntries` + `SkelRel` into `TomlTableEquivList`. -/
  theorem skelMatchesEntries_equiv (skel : List (String × SkeletonNode))
      (e1 e2 : List (String × TomlValue))
      (hm1 : skelMatchesEntries skel e1 = true)
      (hm2 : skelMatchesEntries skel e2 = true)
      (hrel : SkelRel skel e1 e2) : TomlTableEquivList e1 e2 := by
    simp only [skelMatchesEntries, Bool.and_eq_true] at hm1 hm2
    unfold TomlTableEquivList
    constructor
    · intro k hk1
      cases hk2 : lookupKeyList k e2 with
      | none => rfl
      | some v2 =>
        obtain ⟨p, hp, hpk⟩ := lookupKeyList_mem_fst e2 hk2
        have his := List.all_eq_true.mp hm2.1 p hp
        rw [hpk] at his
        cases hlu : assocLookupSkel k skel with
        | none => simp [hlu] at his
        | some sn =>
          obtain ⟨v1, hv1, _⟩ := skelMatchesEntriesAll_lookup skel hm1.2 hlu
          rw [hk1] at hv1; cases hv1
    · intro k v1 hk1
      obtain ⟨p, hp, hpk⟩ := lookupKeyList_mem_fst e1 hk1
      have his := List.all_eq_true.mp hm1.1 p hp
      rw [hpk] at his
      cases hlu : assocLookupSkel k skel with
      | none => simp [hlu] at his
      | some sn =>
        obtain ⟨v1', hv1', hsn1⟩ := skelMatchesEntriesAll_lookup skel hm1.2 hlu
        rw [hk1] at hv1'; injection hv1' with heq; subst heq
        obtain ⟨v2, hk2, hsn2⟩ := skelMatchesEntriesAll_lookup skel hm2.2 hlu
        have hnode := hrel.lookup k sn hlu
        rw [hk1, hk2] at hnode
        have := assocLookupSkel_sizeOf_lt skel hlu
        exact ⟨v2, hk2, skelNodeMatches_equiv sn v1 v2 hsn1 hsn2 hnode⟩
  termination_by sizeOf skel * 2 + 1
  decreasing_by omega

  /-- Convert matching `skelMatchesAot` + `SkelAotRel` into `TomlListEquiv`. -/
  theorem skelMatchesAot_equiv :
      ∀ (elems : List (List (String × SkeletonNode))) (xs1 xs2 : List TomlValue),
        skelMatchesAot elems xs1 = true → skelMatchesAot elems xs2 = true →
        SkelAotRel elems xs1 xs2 → TomlListEquiv xs1 xs2
    | [], xs1, xs2, hm1, hm2, _ => by
      cases xs1 <;> cases xs2 <;> simp [TomlListEquiv, skelMatchesAot] at hm1 hm2 ⊢
    | eSkel :: restSkel, xs1, xs2, hm1, hm2, hrel => by
      cases xs1 with
      | nil => simp [skelMatchesAot] at hm1
      | cons x1 r1 =>
        cases x1 with
        | table d1 =>
          cases xs2 with
          | nil => simp [skelMatchesAot] at hm2
          | cons x2 r2 =>
            cases x2 with
            | table d2 =>
              simp only [skelMatchesAot, Bool.and_eq_true] at hm1 hm2
              simp only [SkelAotRel] at hrel
              unfold TomlListEquiv
              exact ⟨by unfold TomlEquiv; exact skelMatchesEntries_equiv eSkel d1.toList d2.toList hm1.1 hm2.1 hrel.1,
                skelMatchesAot_equiv restSkel r1 r2 hm1.2 hm2.2 hrel.2⟩
            | _ => simp [skelMatchesAot] at hm2
        | _ => simp [skelMatchesAot] at hm1
  termination_by elems _ _ => sizeOf elems * 2
  decreasing_by all_goals simp +arith
end

end LeanSwe.Toml.Proofs

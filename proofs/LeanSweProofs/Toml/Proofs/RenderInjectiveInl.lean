import LeanSweProofs.Toml.Proofs.RenderInjectiveArr

/-!
# Inline-Table & Full `renderValueInline` Prefix-Injectivity

Proves the `.inlineTable` branch and assembles `renderValueInline_injective` across all
`ValueTape` constructors without importing `Toml.Impl`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model

private theorem dk_first_not_rbrace {dk : DottedKeyTape} {rk : String} {c0 : Char} {r0 : List Char}
    (hrk : renderDottedKey dk = some rk) (hl : rk.toList = c0 :: r0) : c0 ≠ '}' := by
  unfold renderDottedKey at hrk
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hrk
  rcases hrk with ⟨rk0, hrk0, _, _, rfl⟩
  cases hfs : dk.firstStyle with
  | bare =>
    rw [hfs] at hrk0; simp only [renderKey] at hrk0; split at hrk0 <;> try (simp at hrk0; done)
    rename_i hb; injection hrk0 with e; subst e
    simp only [isValidBareKey, Bool.and_eq_true] at hb
    simp only [String.toList_append] at hl
    cases hfl : dk.firstKey.toList with
    | nil =>
      have : dk.firstKey = "" := by rw [← String.ofList_toList (s := dk.firstKey), hfl]
      rw [this] at hb; simp at hb
    | cons f0 fs =>
      rw [hfl, List.cons_append] at hl; obtain ⟨rfl, _⟩ := List.cons.inj hl
      exact (isBareKeyChar_not_special (List.all_eq_true.mp hb.2 f0 (by rw [hfl]; simp))).2.2.2.2.2.1
  | basic a? =>
    rw [hfs] at hrk0
    cases a? with
    | none =>
      simp only [renderKey, Option.some.injEq] at hrk0; subst hrk0
      simp [String.toList_append] at hl; obtain ⟨rfl, _⟩ := hl; decide
    | some atoms =>
      simp only [renderKey, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hrk0
      rcases hrk0 with ⟨_, _, rfl⟩; simp [String.toList_append] at hl; obtain ⟨rfl, _⟩ := hl; decide
  | literal =>
    rw [hfs] at hrk0; simp only [renderKey] at hrk0; split at hrk0 <;> try (simp at hrk0; done)
    injection hrk0 with e; subst e; simp [String.toList_append] at hl; obtain ⟨rfl, _⟩ := hl; decide

/-- Inline-table vs inline-table case of `renderValueInline` prefix-injectivity modulo `TomlEquiv`. -/
theorem renderValueInline_inlineTable_injective
    {v1 v2 : TomlValue}
    {as1 as2 : List (String × DottedKeyTape × String × String × ValueTape × String)}
    {ews1 ews2 rs1 rs2 : String} {rem1 rem2 : List Char}
    (ih : ∀ {w1 w2 : TomlValue} {wt1 wt2 : ValueTape} {s1 s2 : String} {rm1 rm2 : List Char},
      sizeOf wt1 < sizeOf (ValueTape.inlineTable as1 ews1) →
      renderValueInline w1 wt1 = some s1 → renderValueInline w2 wt2 = some s2 →
      ModelDelimTail rm1 → ModelDelimTail rm2 →
      s1.toList ++ rm1 = s2.toList ++ rm2 →
      TomlEquiv w1 w2 ∧ rm1 = rm2)
    (hr1 : renderValueInline v1 (.inlineTable as1 ews1) = some rs1)
    (hr2 : renderValueInline v2 (.inlineTable as2 ews2) = some rs2)
    (heq : rs1.toList ++ rem1 = rs2.toList ++ rem2) :
    TomlEquiv v1 v2 ∧ rem1 = rem2 := by
  cases v1 <;> try (simp [renderValueInline] at hr1; done)
  cases v2 <;> try (simp [renderValueInline] at hr2; done)
  rename_i sub1 sub2; unfold renderValueInline at hr1 hr2; dsimp only at hr1 hr2
  if hnd1 : (!noDupKeysBool sub1.toList) = true then simp [hnd1] at hr1 else
  if hnd2 : (!noDupKeysBool sub2.toList) = true then simp [hnd2] at hr2 else
  simp only [hnd1, hnd2, Bool.false_eq_true, ↓reduceIte] at hr1 hr2
  cases as1 with
  | nil =>
    dsimp only at hr1; split at hr1 <;> try (simp at hr1; done)
    rename_i hok1; injection hr1 with hrs1; subst hrs1; simp only [Bool.and_eq_true] at hok1
    cases as2 with
    | nil =>
      dsimp only at hr2; split at hr2 <;> try (simp at hr2; done)
      rename_i hok2; injection hr2 with hrs2; subst hrs2; simp only [Bool.and_eq_true] at hok2
      simp only [String.toList_append, show ("{" : String).toList = ['{'] from rfl,
        show ("}" : String).toList = ['}'] from rfl, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq] at heq
      have hd := congrArg dropHoriz heq.2
      rw [dropHoriz_append hok1.2 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide),
          dropHoriz_append hok2.2 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide)] at hd
      injection hd with _ erem
      have he1 : sub1.toList = [] := Array.toList_eq_nil_iff.mpr (Array.isEmpty_iff.mp hok1.1)
      have he2 : sub2.toList = [] := Array.toList_eq_nil_iff.mpr (Array.isEmpty_iff.mp hok2.1)
      exact ⟨by simp [TomlEquiv, he1, he2, TomlTableEquivList, lookupKeyList], erem⟩
    | cons b0 bs =>
      exfalso
      dsimp only at hr2; split at hr2 <;> try (simp at hr2; done)
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hr2
      rcases hr2 with ⟨⟨lsk2, kvs2⟩, hkvs2, hm2⟩
      split at hm2 <;> try (simp at hm2; done)
      injection hm2 with hrs2; subst hrs2
      rcases b0 with ⟨wP2, dk2, wL2, wR2, vt_c2, wPo2⟩
      unfold renderInlineAssigns at hkvs2; split at hkvs2 <;> try (simp at hkvs2; done)
      rename_i hws2; simp at hws2
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hkvs2
      rcases hkvs2 with ⟨rk2, hrk2, _, _, _, _, ⟨_, _⟩, _, ⟨_, rfl⟩⟩
      obtain ⟨_, _, ck2, _, hrk2_l, hck2⟩ := readDottedKey_renderDottedKey (wsAfter := "") (rem := []) hrk2 rfl (fun _ _ h => nomatch h)
      have hck2_nb := dk_first_not_rbrace hrk2 hrk2_l
      simp only [String.toList_append, show ("{" : String).toList = ['{'] from rfl,
        show ("}" : String).toList = ['}'] from rfl, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq] at heq
      have hd := congrArg dropHoriz heq.2
      rw [dropHoriz_append hok1.2 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide),
          intercalate_comma_cons, List.append_assoc, String.toList_append, String.toList_append,
          String.toList_append, String.toList_append, String.toList_append, String.toList_append,
          List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
          dropHoriz_append hws2.1.1.1 (fun c r h => by rw [hrk2_l, List.cons_append] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; exact hck2.1)] at hd
      rw [hrk2_l, List.cons_append] at hd; injection hd with hbr _; exact hck2_nb hbr.symm
  | cons a0 as1' =>
    dsimp only at hr1; split at hr1 <;> try (simp at hr1; done)
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hr1
    rcases hr1 with ⟨⟨lsk1, kvs1⟩, hkvs1, hm1⟩
    split at hm1 <;> try (simp at hm1; done)
    rename_i hcov1; injection hm1 with hrs1; subst hrs1
    cases as2 with
    | nil =>
      exfalso
      dsimp only at hr2; split at hr2 <;> try (simp at hr2; done)
      rename_i hok2; injection hr2 with hrs2; subst hrs2; simp only [Bool.and_eq_true] at hok2
      rcases a0 with ⟨wP1, dk1, wL1, wR1, vt_c1, wPo1⟩
      unfold renderInlineAssigns at hkvs1; split at hkvs1 <;> try (simp at hkvs1; done)
      rename_i hws1; simp at hws1
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hkvs1
      rcases hkvs1 with ⟨rk1, hrk1, _, _, _, _, ⟨_, _⟩, _, ⟨_, rfl⟩⟩
      obtain ⟨_, _, ck1, _, hrk1_l, hck1⟩ := readDottedKey_renderDottedKey (wsAfter := "") (rem := []) hrk1 rfl (fun _ _ h => nomatch h)
      have hck1_nb := dk_first_not_rbrace hrk1 hrk1_l
      simp only [String.toList_append, show ("{" : String).toList = ['{'] from rfl,
        show ("}" : String).toList = ['}'] from rfl, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq] at heq
      have hd := congrArg dropHoriz heq.2
      rw [dropHoriz_append hok2.2 (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide),
          intercalate_comma_cons, List.append_assoc, String.toList_append, String.toList_append,
          String.toList_append, String.toList_append, String.toList_append, String.toList_append,
          List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
          dropHoriz_append hws1.1.1.1 (fun c r h => by rw [hrk1_l, List.cons_append] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; exact hck1.1)] at hd
      rw [hrk1_l, List.cons_append] at hd; injection hd with hbr _; exact hck1_nb hbr
    | cons b0 bs2' =>
      dsimp only at hr2; split at hr2 <;> try (simp at hr2; done)
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hr2
      rcases hr2 with ⟨⟨lsk2, kvs2⟩, hkvs2, hm2⟩
      split at hm2 <;> try (simp at hm2; done)
      rename_i hcov2; injection hm2 with hrs2; subst hrs2
      simp only [String.toList_append, show ("{" : String).toList = ['{'] from rfl,
        show ("}" : String).toList = ['}'] from rfl, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq] at heq
      have hinl_loop : ∀ (sk : List (String × SkeletonNode))
          (xs1 xs2 : List (String × DottedKeyTape × String × String × ValueTape × String))
          (fsk1 fsk2 : List (String × SkeletonNode)) (ss1 ss2 : List String),
          xs1 ≠ [] → xs2 ≠ [] →
          sizeOf xs1 ≤ sizeOf (a0 :: as1') →
          SkelRel sk sub1.toList sub2.toList →
          renderInlineAssigns sub1.toList sk xs1 = some (fsk1, ss1) →
          renderInlineAssigns sub2.toList sk xs2 = some (fsk2, ss2) →
          (String.intercalate "," ss1).toList ++ ('}' :: rem1) =
          (String.intercalate "," ss2).toList ++ ('}' :: rem2) →
          fsk1 = fsk2 ∧ SkelRel fsk1 sub1.toList sub2.toList ∧ rem1 = rem2 := by
        intro sk xs1; induction xs1 generalizing sk with
        | nil => intro _ _ _ _ _ hne; exact absurd rfl hne
        | cons hd1 tl1 ihl =>
          intro xs2 fsk1 fsk2 ss1 ss2 _ hxs2 hsz_xs hrel hi1 hi2 hstr_eq
          cases xs2 with | nil => exact absurd rfl hxs2 | cons hd2 tl2 =>
          rcases hd1 with ⟨wP1, dk1, wL1, wR1, vt_c1, wPo1⟩
          rcases hd2 with ⟨wP2, dk2, wL2, wR2, vt_c2, wPo2⟩
          unfold renderInlineAssigns at hi1 hi2
          split at hi1 <;> try (simp at hi1; done)
          rename_i hws1; simp at hws1
          split at hi2 <;> try (simp at hi2; done)
          rename_i hws2; simp at hws2
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hi1 hi2
          rcases hi1 with ⟨rk1, hrk1, ⟨nsk1, vc1⟩, hins1, rv1, hrv1, ⟨fsk1', rss1⟩, hrss1, ⟨rfl, rfl⟩⟩
          rcases hi2 with ⟨rk2, hrk2, ⟨nsk2, vc2⟩, hins2, rv2, hrv2, ⟨fsk2', rss2⟩, hrss2, ⟨rfl, rfl⟩⟩
          rw [intercalate_comma_cons', intercalate_comma_cons', List.append_assoc, List.append_assoc] at hstr_eq
          let sep1 := commaRestList rss1 ++ ('}' :: rem1)
          let sep2 := commaRestList rss2 ++ ('}' :: rem2)
          change (wP1 ++ rk1 ++ wL1 ++ "=" ++ wR1 ++ rv1 ++ wPo1).toList ++ sep1 =
                 (wP2 ++ rk2 ++ wL2 ++ "=" ++ wR2 ++ rv2 ++ wPo2).toList ++ sep2 at hstr_eq
          obtain ⟨hrdk1, _, ck1, _, hrk1_l, hck1⟩ := readDottedKey_renderDottedKey hrk1 hws1.1.1.2
            (rem := '=' :: (wR1.toList ++ (rv1.toList ++ (wPo1.toList ++ sep1))))
            (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide)
          obtain ⟨hrdk2, _, ck2, _, hrk2_l, hck2⟩ := readDottedKey_renderDottedKey hrk2 hws2.1.1.2
            (rem := '=' :: (wR2.toList ++ (rv2.toList ++ (wPo2.toList ++ sep2))))
            (fun c r h => by obtain ⟨rfl, _⟩ := List.cons.inj h; decide)
          have hd_pre := congrArg dropHoriz hstr_eq
          simp only [String.toList_append, show ("=" : String).toList = ['='] from rfl, List.cons_append, List.nil_append, List.append_assoc] at hd_pre
          rw [dropHoriz_append hws1.1.1.1 (fun c r h => by rw [hrk1_l, List.cons_append] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; exact hck1.1),
              dropHoriz_append hws2.1.1.1 (fun c r h => by rw [hrk2_l, List.cons_append] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; exact hck2.1)] at hd_pre
          rw [List.append_assoc] at hrdk1 hrdk2
          have hrdk_eq := hrdk1.symm.trans ((congrArg readDottedKey hd_pre).trans hrdk2)
          injection hrdk_eq with hp_eq; injection hp_eq with hpath_eq heq_part
          injection heq_part with _ hafter_eq
          obtain ⟨_, cv1, _, hrv1_l, hnd_v1, _⟩ := renderValueInline_head hrv1
          obtain ⟨_, cv2, _, hrv2_l, hnd_v2, _⟩ := renderValueInline_head hrv2
          have hd_eqr := congrArg dropHoriz hafter_eq
          rw [dropHoriz_append hws1.1.2 (fun c r h => by rw [hrv1_l, List.cons_append] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; exact (not_triv_of_valHead hnd_v1).1),
              dropHoriz_append hws2.1.2 (fun c r h => by rw [hrv2_l, List.cons_append] at h; obtain ⟨rfl, _⟩ := List.cons.inj h; exact (not_triv_of_valHead hnd_v2).1)] at hd_eqr
          have hsep_hd (rss : List String) (rem : List Char) :
              ∃ cEnd af, commaRestList rss ++ ('}' :: rem) = cEnd :: af ∧
                (cEnd = ',' ∨ cEnd = '}' ∨ cEnd = '#' ∨ cEnd = '\n') := by
            cases rss with
            | nil => exact ⟨'}', rem, rfl, Or.inr (Or.inl rfl)⟩
            | cons _ _ => exact ⟨',', _, rfl, Or.inl rfl⟩
          obtain ⟨ce1, af1, hsp1_eq, hce1⟩ := hsep_hd rss1 rem1
          obtain ⟨ce2, af2, hsp2_eq, hce2⟩ := hsep_hd rss2 rem2
          have hdt1 : ModelDelimTail (wPo1.toList ++ sep1) := by dsimp only [sep1]; rw [hsp1_eq]; exact horizWs_delimTail hws1.2 hce1
          have hdt2 : ModelDelimTail (wPo2.toList ++ sep2) := by dsimp only [sep2]; rw [hsp2_eq]; exact horizWs_delimTail hws2.2 hce2
          obtain ⟨heqv_c, hwpo_eq⟩ := ih (by simp +arith at hsz_xs ⊢; omega) hrv1 hrv2 hdt1 hdt2 hd_eqr
          obtain ⟨rfl, hrel_next⟩ := insertDottedAndLookup_rel dk1.path sk nsk1 nsk2
            sub1.toList sub2.toList vc1 vc2 hrel hins1 (hpath_eq ▸ hins2) heqv_c
          have hsep_eq : sep1 = sep2 := by
            have hd := congrArg dropHoriz hwpo_eq
            rwa [dropHoriz_append hws1.2 (by dsimp only [sep1]; rw [hsp1_eq]; intro c r h; obtain ⟨rfl, _⟩ := List.cons.inj h; rcases hce1 with rfl | rfl | rfl | rfl <;> decide),
                 dropHoriz_append hws2.2 (by dsimp only [sep2]; rw [hsp2_eq]; intro c r h; obtain ⟨rfl, _⟩ := List.cons.inj h; rcases hce2 with rfl | rfl | rfl | rfl <;> decide)] at hd
          have rss_empty_iff (tl : List (String × DottedKeyTape × String × String × ValueTape × String))
              (es : List (String × TomlValue)) (fsk : List (String × SkeletonNode)) (rss : List String)
              (hr : renderInlineAssigns es nsk1 tl = some (fsk, rss)) : tl = [] ↔ rss = [] := by
            cases tl with
            | nil => simp [renderInlineAssigns] at hr; exact ⟨fun _ => hr.2, fun _ => rfl⟩
            | cons h _ =>
              rcases h with ⟨_, _, _, _, _, _⟩
              unfold renderInlineAssigns at hr; split at hr
              · nomatch hr
              · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hr
                rcases hr with ⟨_, _, _, _, _, _, ⟨_, _⟩, _, ⟨_, rfl⟩⟩; simp
          cases tl1 with
          | nil =>
            simp only [renderInlineAssigns, Option.some.injEq, Prod.mk.injEq] at hrss1
            rcases hrss1 with ⟨rfl, rfl⟩
            cases tl2 with
            | nil =>
              simp only [renderInlineAssigns, Option.some.injEq, Prod.mk.injEq] at hrss2
              rcases hrss2 with ⟨rfl, rfl⟩
              dsimp only [sep1, sep2, commaRestList] at hsep_eq; injection hsep_eq with _ erem
              exact ⟨rfl, hrel_next, erem⟩
            | cons h2 t2 =>
              have hne2 : rss2 ≠ [] := fun e => by have := (rss_empty_iff (h2 :: t2) sub2.toList fsk2' rss2 hrss2).mpr e; nomatch this
              cases rss2 with | nil => exact absurd rfl hne2 | cons _ _ => dsimp only [sep1, sep2, commaRestList] at hsep_eq; cases hsep_eq
          | cons h1 t1 =>
            have hne1 : rss1 ≠ [] := fun e => by have := (rss_empty_iff (h1 :: t1) sub1.toList fsk1' rss1 hrss1).mpr e; nomatch this
            cases rss1 with
            | nil => exact absurd rfl hne1
            | cons s1_n sr1 =>
              cases tl2 with
              | nil =>
                simp only [renderInlineAssigns, Option.some.injEq, Prod.mk.injEq] at hrss2
                rcases hrss2 with ⟨_, rfl⟩; dsimp only [sep1, sep2, commaRestList] at hsep_eq; cases hsep_eq
              | cons h2 t2 =>
                have hne2 : rss2 ≠ [] := fun e => by have := (rss_empty_iff (h2 :: t2) sub2.toList fsk2' rss2 hrss2).mpr e; nomatch this
                cases rss2 with
                | nil => exact absurd rfl hne2
                | cons s2_n sr2 =>
                  dsimp only [sep1, sep2, commaRestList] at hsep_eq
                  simp only [List.cons_append, List.cons.injEq] at hsep_eq
                  exact ihl nsk1 (h2 :: t2) fsk1' fsk2' (s1_n :: sr1) (s2_n :: sr2)
                    (by simp) (by simp) (by simp +arith at hsz_xs ⊢; omega) hrel_next hrss1 hrss2 hsep_eq.2
      obtain ⟨rfl, hrel_fin, erem⟩ := hinl_loop [] (a0 :: as1') (b0 :: bs2') lsk1 lsk2 kvs1 kvs2
        (by simp) (by simp) (Nat.le_refl _) (skelRel_nil _ _) hkvs1 hkvs2 heq.2
      exact ⟨by unfold TomlEquiv; exact skelMatchesEntries_equiv lsk1 sub1.toList sub2.toList hcov1 hcov2 hrel_fin, erem⟩

/-- Full prefix-injectivity of `renderValueInline` modulo `TomlEquiv`. -/
theorem renderValueInline_injective :
    ∀ (n : Nat) {v1 v2 : TomlValue} {vt1 vt2 : ValueTape} {rs1 rs2 : String} {rem1 rem2 : List Char},
      sizeOf vt1 ≤ n →
      renderValueInline v1 vt1 = some rs1 → renderValueInline v2 vt2 = some rs2 →
      ModelDelimTail rem1 → ModelDelimTail rem2 →
      rs1.toList ++ rem1 = rs2.toList ++ rem2 →
      TomlEquiv v1 v2 ∧ rem1 = rem2 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro v1 v2 vt1 vt2 rs1 rs2 rem1 rem2 hsz hr1 hr2 hd1 hd2 heq
    obtain ⟨_, c1, r1, hl1, hdel1, hcat1⟩ := renderValueInline_head hr1
    obtain ⟨_, c2, r2, hl2, hdel2, hcat2⟩ := renderValueInline_head hr2
    have hc12 : c1 = c2 := by rw [hl1, hl2, List.cons_append, List.cons_append] at heq; exact (List.cons.inj heq).1
    subst hc12
    cases vt1 with
    | string st1 =>
      cases vt2 with
      | string st2 =>
        cases v1 <;> try (simp [renderValueInline] at hr1; done)
        cases v2 <;> try (simp [renderValueInline] at hr2; done)
        simp only [renderValueInline] at hr1 hr2
        have nq (rem : List Char) (hd : ModelDelimTail rem) : ∀ c r, rem = c :: r → c ≠ '"' ∧ c ≠ '\'' := by
          intro c r hcr; have hm := (hd c r hcr).1
          exact ⟨by intro heq; subst heq; revert hm; decide, by intro heq; subst heq; revert hm; decide⟩
        have hs1 := (readStringVal_renderStringLiteral hr1 (nq rem1 hd1)).1
        have hs2 := (readStringVal_renderStringLiteral hr2 (nq rem2 hd2)).1
        have h := hs1.symm.trans ((congrArg readStringVal heq).trans hs2)
        injection h with hp; injection hp with es erem
        exact ⟨by simp [TomlEquiv, es], erem⟩
      | array _ _ => dsimp only at hcat1 hcat2; rcases hcat1 with rfl | rfl <;> cases hcat2
      | inlineTable _ _ => dsimp only at hcat1 hcat2; rcases hcat1 with rfl | rfl <;> cases hcat2
      | _ => dsimp only at hcat1 hcat2; rcases hcat1 with rfl | rfl <;> first | exact absurd rfl hcat2.1 | exact absurd rfl hcat2.2.1
    | array tps1 tr1 =>
      cases vt2 with
      | string _ => dsimp only at hcat1 hcat2; subst hcat1; rcases hcat2 with h | h <;> cases h
      | inlineTable _ _ => dsimp only at hcat1 hcat2; subst hcat1; cases hcat2
      | int _ | float _ | bool | offsetDateTime _ _ _ | localDateTime _ _ | localDate | localTime _ =>
        dsimp only at hcat1 hcat2; subst hcat1; exact absurd rfl hcat2.2.2.1
      | array tps2 tr2 =>
        exact renderValueInline_array_injective
          (fun {w1 w2 wt1 wt2 s1 s2 rm1 rm2} hlt => ih (sizeOf wt1) (Nat.lt_of_lt_of_le hlt hsz) (Nat.le_refl _))
          hr1 hr2 heq
    | inlineTable as1 ews1 =>
      cases vt2 with
      | string _ => dsimp only at hcat1 hcat2; subst hcat1; rcases hcat2 with h | h <;> cases h
      | array _ _ => dsimp only at hcat1 hcat2; subst hcat1; cases hcat2
      | int _ | float _ | bool | offsetDateTime _ _ _ | localDateTime _ _ | localDate | localTime _ =>
        dsimp only at hcat1 hcat2; subst hcat1; exact absurd rfl hcat2.2.2.2
      | inlineTable as2 ews2 =>
        exact renderValueInline_inlineTable_injective
          (fun {w1 w2 wt1 wt2 s1 s2 rm1 rm2} hlt => ih (sizeOf wt1) (Nat.lt_of_lt_of_le hlt hsz) (Nat.le_refl _))
          hr1 hr2 heq
    | int _ | float _ | bool | offsetDateTime _ _ _ | localDateTime _ _ | localDate | localTime _ =>
      cases vt2 with
      | string _ => dsimp only at hcat1 hcat2; rcases hcat2 with rfl | rfl <;> first | exact absurd rfl hcat1.1 | exact absurd rfl hcat1.2.1
      | array _ _ => dsimp only at hcat1 hcat2; subst hcat2; exact absurd rfl hcat1.2.2.1
      | inlineTable _ _ => dsimp only at hcat1 hcat2; subst hcat2; exact absurd rfl hcat1.2.2.2
      | int _ | float _ | bool | offsetDateTime _ _ _ | localDateTime _ _ | localDate | localTime _ =>
        exact unquotedScalar_injective rfl rfl hr1 hr2 hd1 hd2 heq

end LeanSwe.Toml.Proofs

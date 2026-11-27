import Core.Obeys
import LeanSweProofs.Toml.Proofs.RenderInjectiveInl

/-!
# Standalone `Core.RenderInjectiveModulo` Proof for `Toml.Model.render`

Proves `render_injective_model : Core.RenderInjectiveModulo Model.render Model.TomlTableEquiv`
purely on `LeanSwe.Toml.Model` (zero `LeanSwe.Toml.Impl` dependency).
-/

namespace LeanSwe.Toml.Proofs

open Core
open LeanSwe.Toml
open LeanSwe.Toml.Model

private theorem noCr_renderStmts {docEntries : List (String × TomlValue)} {trailingNl : Bool} :
    ∀ (stmts : List StmtTape) (activePath : List String) (skel finalSkel : List (String × SkeletonNode)) (bodyStr : String),
      renderStmts docEntries activePath skel trailingNl stmts = some (finalSkel, bodyStr) →
      NoCrStr bodyStr
  | [], _, _, _, bodyStr, h => by
    simp only [renderStmts, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨_, rfl⟩; decide
  | stmt :: rest, activePath, skel, finalSkel, bodyStr, h => by
    have hle_cr : NoCrStr (if rest.isEmpty then (if trailingNl then "\n" else "") else "\n") := by
      cases rest.isEmpty <;> cases trailingNl <;> decide
    cases stmt with
    | tableHeader pre wsO dk wsC suf =>
      unfold renderStmts at h; dsimp only at h
      split at h <;> try (simp at h; done)
      rename_i hok; simp at hok
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rk, hrk, rsuf, hsuf, nsk, _, ⟨fsk, tl⟩, htl, ⟨rfl, rfl⟩⟩
      obtain ⟨_, hrk_cr, _⟩ := readDottedKey_renderDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ e => nomatch e)
      obtain ⟨_, hsuf_cr⟩ := dropLineEnd_append (lineEnd := "\n") (tail := []) hsuf (Or.inl rfl)
      exact noCrStr_append (noCrStr_append (noCrStr_append (noCrStr_append (noCrStr_append
        (noCrStr_append (noCrStr_append (noCrStr_append
          (noCr_closedTrivia hok.1.1) (by decide)) (noCr_horizWsStr hok.1.2)) hrk_cr)
          (noCr_horizWsStr hok.2)) (by decide)) hsuf_cr) hle_cr)
        (noCr_renderStmts rest dk.path nsk fsk tl htl)
    | aotHeader pre wsO dk wsC suf =>
      unfold renderStmts at h; dsimp only at h
      split at h <;> try (simp at h; done)
      rename_i hok; simp at hok
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rk, hrk, rsuf, hsuf, nsk, _, ⟨fsk, tl⟩, htl, ⟨rfl, rfl⟩⟩
      obtain ⟨_, hrk_cr, _⟩ := readDottedKey_renderDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ e => nomatch e)
      obtain ⟨_, hsuf_cr⟩ := dropLineEnd_append (lineEnd := "\n") (tail := []) hsuf (Or.inl rfl)
      exact noCrStr_append (noCrStr_append (noCrStr_append (noCrStr_append (noCrStr_append
        (noCrStr_append (noCrStr_append (noCrStr_append
          (noCr_closedTrivia hok.1.1) (by decide)) (noCr_horizWsStr hok.1.2)) hrk_cr)
          (noCr_horizWsStr hok.2)) (by decide)) hsuf_cr) hle_cr)
        (noCr_renderStmts rest dk.path nsk fsk tl htl)
    | assign pre dk wsL wsR vt suf =>
      unfold renderStmts at h; dsimp only at h
      split at h <;> try (simp at h; done)
      rename_i hok; simp at hok
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rk, hrk, rsuf, hsuf, ⟨nsk, v⟩, _, rv, hrv, ⟨fsk, tl⟩, htl, ⟨rfl, rfl⟩⟩
      obtain ⟨_, hrk_cr, _⟩ := readDottedKey_renderDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ e => nomatch e)
      obtain ⟨_, hsuf_cr⟩ := dropLineEnd_append (lineEnd := "\n") (tail := []) hsuf (Or.inl rfl)
      exact noCrStr_append (noCrStr_append (noCrStr_append (noCrStr_append (noCrStr_append
        (noCrStr_append (noCrStr_append (noCrStr_append
          (noCr_closedTrivia hok.1.1) hrk_cr) (noCr_horizWsStr hok.1.2)) (by decide))
          (noCr_horizWsStr hok.2)) (renderValueInline_head hrv).1) hsuf_cr) hle_cr)
        (noCr_renderStmts rest activePath nsk fsk tl htl)

private theorem noCr_renderLF {doc : TomlTable} {tape : RenderTape} {lf : String}
    (hr : renderLF doc tape = some lf) : NoCrStr lf := by
  unfold renderLF at hr
  if h1 : (!wellFormedTableBool doc) = true then simp [h1] at hr else
  if h2 : (!tape.stmts.isEmpty && !tape.trailingNewline && !tape.eofTrivia.isEmpty) = true then simp [h1, h2] at hr else
  if h3 : (!isEofTrivia tape.eofTrivia) = true then simp [h1, h2, h3] at hr else
  simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
  rcases hr with ⟨⟨fsk, body⟩, hbody, hm⟩
  split at hm <;> try (simp at hm; done)
  injection hm with hlf; subst hlf
  have heof : isEofTrivia tape.eofTrivia = true := by cases hi : isEofTrivia tape.eofTrivia <;> simp_all
  exact noCrStr_append (noCr_renderStmts tape.stmts [] [] fsk body hbody) (noCr_eofTrivia heof)

private theorem stmt_dropTrivia_shape {docEntries : List (String × TomlValue)} {activePath : List String}
    {skel finalSkel : List (String × SkeletonNode)} {trailingNl : Bool}
    {stmt : StmtTape} {rest : List StmtTape} {bodyStr eof : String}
    (hr : renderStmts docEntries activePath skel trailingNl (stmt :: rest) = some (finalSkel, bodyStr)) :
    ∃ c1 tailCs, dropTrivia false ((bodyStr ++ eof).toList) = c1 :: tailCs ∧
      match stmt with
      | .tableHeader _ _ _ _ _ => c1 = '[' ∧ ∃ c2 r2, tailCs = c2 :: r2 ∧ c2 ≠ '['
      | .aotHeader _ _ _ _ _ => c1 = '[' ∧ ∃ r2, tailCs = '[' :: r2
      | .assign _ _ _ _ _ _ => c1 ≠ '[' := by
  cases stmt with
  | tableHeader pre wsO dk wsC suf =>
    unfold renderStmts at hr; dsimp only at hr
    split at hr <;> try (simp at hr; done)
    rename_i hok; simp at hok
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rk, hrk, rsuf, _, nsk, _, ⟨fsk, tl⟩, _, ⟨rfl, rfl⟩⟩
    obtain ⟨_, _, ck, rkr, hrk_l, hck⟩ := readDottedKey_renderDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ e => nomatch e)
    simp only [String.toList_append, List.append_assoc, show ("[" : String).toList = ['['] from rfl, List.cons_append, List.nil_append]
    rw [dropTrivia_closed_append false pre.toList _ hok.1.1 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)]
    refine ⟨'[', _, rfl, rfl, ?_⟩
    cases hwl : wsO.toList with
    | nil =>
      rw [List.nil_append, hrk_l, List.cons_append]
      exact ⟨ck, _, rfl, hck.2.2.2⟩
    | cons w0 ws =>
      rw [List.cons_append]
      have hw0 := List.all_eq_true.mp hok.1.2 w0 (by rw [hwl]; simp)
      exact ⟨w0, _, rfl, by intro heq; subst heq; revert hw0; decide⟩
  | aotHeader pre wsO dk wsC suf =>
    unfold renderStmts at hr; dsimp only at hr
    split at hr <;> try (simp at hr; done)
    rename_i hok; simp at hok
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rk, _, rsuf, _, nsk, _, ⟨fsk, tl⟩, _, ⟨rfl, rfl⟩⟩
    simp only [String.toList_append, List.append_assoc, show ("[[" : String).toList = ['[', '['] from rfl, List.cons_append, List.nil_append]
    rw [dropTrivia_closed_append false pre.toList _ hok.1.1 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)]
    exact ⟨'[', _, rfl, rfl, _, rfl⟩
  | assign pre dk wsL wsR vt suf =>
    unfold renderStmts at hr; dsimp only at hr
    split at hr <;> try (simp at hr; done)
    rename_i hok; simp at hok
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rk, hrk, rsuf, _, ⟨nsk, v⟩, _, rv, _, ⟨fsk, tl⟩, _, ⟨rfl, rfl⟩⟩
    obtain ⟨_, _, ck, rkr, hrk_l, hck⟩ := readDottedKey_renderDottedKey (wsAfter := "") (rem := []) hrk rfl (fun _ _ e => nomatch e)
    simp only [String.toList_append, List.append_assoc]
    rw [dropTrivia_closed_append false pre.toList _ hok.1.1 (fun c r e => by
      rw [hrk_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact ⟨hck.1, hck.2.1, hck.2.2.1⟩)]
    rw [hrk_l, List.cons_append]
    exact ⟨ck, _, rfl, hck.2.2.2⟩

private theorem lineEnd_cases {docEntries : List (String × TomlValue)} {activePath : List String}
    {nsk fsk : List (String × SkeletonNode)} {trailingNl : Bool} {rest : List StmtTape}
    {tl eof : String}
    (htl : renderStmts docEntries activePath nsk trailingNl rest = some (fsk, tl))
    (heof_empty : trailingNl = false → rest = [] → eof = "") :
    let lineEnd := if rest.isEmpty then (if trailingNl then "\n" else "") else "\n"
    (lineEnd = "\n") ∨ (lineEnd = "" ∧ tl.toList ++ eof.toList = []) := by
  cases rest with
  | cons _ _ => exact Or.inl rfl
  | nil =>
    simp only [renderStmts, Option.some.injEq, Prod.mk.injEq] at htl
    rcases htl with ⟨_, rfl⟩
    cases trailingNl with
    | true => exact Or.inl rfl
    | false =>
      rw [heof_empty rfl rfl]
      exact Or.inr ⟨rfl, rfl⟩

/-- Statement-list injectivity: two rendered `StmtTape` sequences producing equal LF streams yield identical skeletons and `SkelRel`. -/
theorem renderStmts_injective {e1 e2 : List (String × TomlValue)} {tnl1 tnl2 : Bool} {eof1 eof2 : String}
    (heof1_tr : isEofTrivia eof1 = true) (heof2_tr : isEofTrivia eof2 = true) :
    ∀ (stmts1 stmts2 : List StmtTape) (activePath : List String)
      (skel fsk1 fsk2 : List (String × SkeletonNode)) (body1 body2 : String),
      (tnl1 = false → stmts1 ≠ [] → eof1 = "") →
      (tnl2 = false → stmts2 ≠ [] → eof2 = "") →
      skelEntriesWF skel = true →
      SkelRel skel e1 e2 →
      renderStmts e1 activePath skel tnl1 stmts1 = some (fsk1, body1) →
      renderStmts e2 activePath skel tnl2 stmts2 = some (fsk2, body2) →
      body1.toList ++ eof1.toList = body2.toList ++ eof2.toList →
      fsk1 = fsk2 ∧ SkelRel fsk1 e1 e2
  | [], [], _, skel, fsk1, fsk2, body1, body2, _, _, _, hrel, hr1, hr2, _ => by
    simp only [renderStmts, Option.some.injEq, Prod.mk.injEq] at hr1 hr2
    rcases hr1 with ⟨rfl, _⟩; rcases hr2 with ⟨rfl, _⟩
    exact ⟨rfl, hrel⟩
  | [], s2 :: r2, activePath, skel, fsk1, fsk2, body1, body2, _, _, _, _, hr1, hr2, heq => by
    exfalso
    simp only [renderStmts, Option.some.injEq, Prod.mk.injEq] at hr1; rcases hr1 with ⟨_, rfl⟩
    obtain ⟨c1, tcs, hsh2, _⟩ := stmt_dropTrivia_shape (eof := eof2) hr2
    rw [String.toList_append, ← heq, show ("" : String).toList = [] from rfl, List.nil_append,
        dropTrivia_eof false _ heof1_tr] at hsh2
    cases hsh2
  | s1 :: r1, [], activePath, skel, fsk1, fsk2, body1, body2, _, _, _, _, hr1, hr2, heq => by
    exfalso
    simp only [renderStmts, Option.some.injEq, Prod.mk.injEq] at hr2; rcases hr2 with ⟨_, rfl⟩
    obtain ⟨c1, tcs, hsh1, _⟩ := stmt_dropTrivia_shape (eof := eof1) hr1
    rw [String.toList_append, heq, show ("" : String).toList = [] from rfl, List.nil_append,
        dropTrivia_eof false _ heof2_tr] at hsh1
    cases hsh1
  | s1 :: r1, s2 :: r2, activePath, skel, fsk1, fsk2, body1, body2, hne1, hne2, hwf, hrel, hr1, hr2, heq => by
    have heof1_nil : tnl1 = false → eof1 = "" := fun ht => hne1 ht (by simp)
    have heof2_nil : tnl2 = false → eof2 = "" := fun ht => hne2 ht (by simp)
    obtain ⟨ch1, tcs1, hsh1, hcat1⟩ := stmt_dropTrivia_shape (eof := eof1) hr1
    obtain ⟨ch2, tcs2, hsh2, hcat2⟩ := stmt_dropTrivia_shape (eof := eof2) hr2
    have hsh_eq : ch1 :: tcs1 = ch2 :: tcs2 := by
      rw [← hsh1, ← hsh2, String.toList_append, String.toList_append, heq]
    injection hsh_eq with hch htcs
    subst hch
    cases s1 with
    | tableHeader pre1 wsO1 dk1 wsC1 suf1 =>
      cases s2 with
      | aotHeader _ _ _ _ _ =>
        dsimp only at hcat1 hcat2; rcases hcat1 with ⟨_, c2, r2, ht1, hne⟩; rcases hcat2 with ⟨_, r2', ht2⟩
        rw [ht1, ht2] at htcs; injection htcs with h _; exact absurd h hne
      | assign _ _ _ _ _ _ =>
        dsimp only at hcat1 hcat2; exact absurd hcat1.1 hcat2
      | tableHeader pre2 wsO2 dk2 wsC2 suf2 =>
        unfold renderStmts at hr1 hr2; dsimp only at hr1 hr2
        split at hr1 <;> try (simp at hr1; done)
        rename_i hok1; simp at hok1
        split at hr2 <;> try (simp at hr2; done)
        rename_i hok2; simp at hok2
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hr1 hr2
        rcases hr1 with ⟨rk1, hrk1, rsuf1, hsuf1, nsk1, hhdr1, ⟨fsk1', tl1⟩, htl1, ⟨rfl, rfl⟩⟩
        rcases hr2 with ⟨rk2, hrk2, rsuf2, hsuf2, nsk2, hhdr2, ⟨fsk2', tl2⟩, htl2, ⟨rfl, rfl⟩⟩
        let le1 := if r1.isEmpty then (if tnl1 then "\n" else "") else "\n"
        let le2 := if r2.isEmpty then (if tnl2 then "\n" else "") else "\n"
        have hle1 := lineEnd_cases htl1 (fun ht _ => heof1_nil ht)
        have hle2 := lineEnd_cases htl2 (fun ht _ => heof2_nil ht)
        obtain ⟨hrdk1, _, ck1, _, hrk1_l, hck1⟩ := readDottedKey_renderDottedKey hrk1 hok1.2
          (rem := ']' :: ((rsuf1 ++ le1).toList ++ (tl1.toList ++ eof1.toList)))
          (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)
        obtain ⟨hrdk2, _, ck2, _, hrk2_l, hck2⟩ := readDottedKey_renderDottedKey hrk2 hok2.2
          (rem := ']' :: ((rsuf2 ++ le2).toList ++ (tl2.toList ++ eof2.toList)))
          (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)
        simp only [String.toList_append, List.append_assoc] at hrdk1 hrdk2
        have hd0 := congrArg (dropTrivia false) heq
        simp only [String.toList_append, List.append_assoc, show ("[" : String).toList = ['['] from rfl,
          show ("]" : String).toList = [']'] from rfl, List.cons_append, List.nil_append] at hd0
        rw [dropTrivia_closed_append false pre1.toList _ hok1.1.1 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide),
            dropTrivia_closed_append false pre2.toList _ hok2.1.1 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)] at hd0
        injection hd0 with _ hd1
        have hd2 := congrArg dropHoriz hd1
        rw [dropHoriz_append hok1.1.2 (fun c r e => by rw [hrk1_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact hck1.1),
            dropHoriz_append hok2.1.2 (fun c r e => by rw [hrk2_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact hck2.1)] at hd2
        have hrdk_eq := hrdk1.symm.trans ((congrArg readDottedKey hd2).trans hrdk2)
        injection hrdk_eq with hp; injection hp with hpath hbr_eq
        injection hbr_eq with _ hsuf_eq
        have htail_eq : tl1.toList ++ eof1.toList = tl2.toList ++ eof2.toList := by
          have hd := congrArg dropLineEnd hsuf_eq
          have h1' := (dropLineEnd_append (suf := suf1) (rsuf := rsuf1) (lineEnd := le1) hsuf1 hle1).1
          have h2' := (dropLineEnd_append (suf := suf2) (rsuf := rsuf2) (lineEnd := le2) hsuf2 hle2).1
          simp only [String.toList_append, List.append_assoc] at h1' h2'
          rwa [h1', h2'] at hd
        have hnsk_eq : nsk1 = nsk2 := Option.some.inj (hhdr1.symm.trans (hpath ▸ hhdr2))
        subst hnsk_eq
        obtain ⟨hwf_n, hrel_n⟩ := applyHeaderSkel_preserves false dk1.path skel nsk1 hwf hhdr1
        exact renderStmts_injective heof1_tr heof2_tr r1 r2 dk1.path nsk1 fsk1' fsk2' tl1 tl2
          (fun ht _ => heof1_nil ht) (fun ht _ => heof2_nil ht) hwf_n (hrel_n _ _ hrel)
          htl1 (hpath ▸ htl2) htail_eq
    | aotHeader pre1 wsO1 dk1 wsC1 suf1 =>
      cases s2 with
      | tableHeader _ _ _ _ _ =>
        dsimp only at hcat1 hcat2; rcases hcat1 with ⟨_, r2', ht1⟩; rcases hcat2 with ⟨_, c2, r2, ht2, hne⟩
        rw [ht1, ht2] at htcs; injection htcs with h _; exact absurd h.symm hne
      | assign _ _ _ _ _ _ =>
        dsimp only at hcat1 hcat2; exact absurd hcat1.1 hcat2
      | aotHeader pre2 wsO2 dk2 wsC2 suf2 =>
        unfold renderStmts at hr1 hr2; dsimp only at hr1 hr2
        split at hr1 <;> try (simp at hr1; done)
        rename_i hok1; simp at hok1
        split at hr2 <;> try (simp at hr2; done)
        rename_i hok2; simp at hok2
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hr1 hr2
        rcases hr1 with ⟨rk1, hrk1, rsuf1, hsuf1, nsk1, hhdr1, ⟨fsk1', tl1⟩, htl1, ⟨rfl, rfl⟩⟩
        rcases hr2 with ⟨rk2, hrk2, rsuf2, hsuf2, nsk2, hhdr2, ⟨fsk2', tl2⟩, htl2, ⟨rfl, rfl⟩⟩
        let le1 := if r1.isEmpty then (if tnl1 then "\n" else "") else "\n"
        let le2 := if r2.isEmpty then (if tnl2 then "\n" else "") else "\n"
        have hle1 := lineEnd_cases htl1 (fun ht _ => heof1_nil ht)
        have hle2 := lineEnd_cases htl2 (fun ht _ => heof2_nil ht)
        obtain ⟨hrdk1, _, ck1, _, hrk1_l, hck1⟩ := readDottedKey_renderDottedKey hrk1 hok1.2
          (rem := ']' :: ']' :: ((rsuf1 ++ le1).toList ++ (tl1.toList ++ eof1.toList)))
          (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)
        obtain ⟨hrdk2, _, ck2, _, hrk2_l, hck2⟩ := readDottedKey_renderDottedKey hrk2 hok2.2
          (rem := ']' :: ']' :: ((rsuf2 ++ le2).toList ++ (tl2.toList ++ eof2.toList)))
          (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)
        simp only [String.toList_append, List.append_assoc] at hrdk1 hrdk2
        have hd0 := congrArg (dropTrivia false) heq
        simp only [String.toList_append, List.append_assoc,
          show ("[[" : String).toList = ['[', '['] from rfl,
          show ("]]" : String).toList = [']', ']'] from rfl, List.cons_append, List.nil_append] at hd0
        rw [dropTrivia_closed_append false pre1.toList _ hok1.1.1 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide),
            dropTrivia_closed_append false pre2.toList _ hok2.1.1 (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)] at hd0
        injection hd0 with _ hd0'; injection hd0' with _ hd1
        have hd2 := congrArg dropHoriz hd1
        rw [dropHoriz_append hok1.1.2 (fun c r e => by rw [hrk1_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact hck1.1),
            dropHoriz_append hok2.1.2 (fun c r e => by rw [hrk2_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact hck2.1)] at hd2
        have hrdk_eq := hrdk1.symm.trans ((congrArg readDottedKey hd2).trans hrdk2)
        injection hrdk_eq with hp; injection hp with hpath hbr_eq
        injection hbr_eq with _ hbr_eq2; injection hbr_eq2 with _ hsuf_eq
        have htail_eq : tl1.toList ++ eof1.toList = tl2.toList ++ eof2.toList := by
          have hd := congrArg dropLineEnd hsuf_eq
          have h1' := (dropLineEnd_append (suf := suf1) (rsuf := rsuf1) (lineEnd := le1) hsuf1 hle1).1
          have h2' := (dropLineEnd_append (suf := suf2) (rsuf := rsuf2) (lineEnd := le2) hsuf2 hle2).1
          simp only [String.toList_append, List.append_assoc] at h1' h2'
          rwa [h1', h2'] at hd
        have hnsk_eq : nsk1 = nsk2 := Option.some.inj (hhdr1.symm.trans (hpath ▸ hhdr2))
        subst hnsk_eq
        obtain ⟨hwf_n, hrel_n⟩ := applyHeaderSkel_preserves true dk1.path skel nsk1 hwf hhdr1
        exact renderStmts_injective heof1_tr heof2_tr r1 r2 dk1.path nsk1 fsk1' fsk2' tl1 tl2
          (fun ht _ => heof1_nil ht) (fun ht _ => heof2_nil ht) hwf_n (hrel_n _ _ hrel)
          htl1 (hpath ▸ htl2) htail_eq
    | assign pre1 dk1 wsL1 wsR1 vt1 suf1 =>
      cases s2 with
      | tableHeader _ _ _ _ _ => dsimp only at hcat1 hcat2; exact absurd hcat2.1 hcat1
      | aotHeader _ _ _ _ _ => dsimp only at hcat1 hcat2; exact absurd hcat2.1 hcat1
      | assign pre2 dk2 wsL2 wsR2 vt2 suf2 =>
        unfold renderStmts at hr1 hr2; dsimp only at hr1 hr2
        split at hr1 <;> try (simp at hr1; done)
        rename_i hok1; simp at hok1
        split at hr2 <;> try (simp at hr2; done)
        rename_i hok2; simp at hok2
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hr1 hr2
        rcases hr1 with ⟨rk1, hrk1, rsuf1, hsuf1, ⟨nsk1, v1⟩, hins1, rv1, hrv1, ⟨fsk1', tl1⟩, htl1, ⟨rfl, rfl⟩⟩
        rcases hr2 with ⟨rk2, hrk2, rsuf2, hsuf2, ⟨nsk2, v2⟩, hins2, rv2, hrv2, ⟨fsk2', tl2⟩, htl2, ⟨rfl, rfl⟩⟩
        let le1 := if r1.isEmpty then (if tnl1 then "\n" else "") else "\n"
        let le2 := if r2.isEmpty then (if tnl2 then "\n" else "") else "\n"
        have hle1 := lineEnd_cases htl1 (fun ht _ => heof1_nil ht)
        have hle2 := lineEnd_cases htl2 (fun ht _ => heof2_nil ht)
        obtain ⟨hrdk1, _, ck1, _, hrk1_l, hck1⟩ := readDottedKey_renderDottedKey hrk1 hok1.1.2
          (rem := '=' :: (wsR1.toList ++ (rv1.toList ++ ((rsuf1 ++ le1).toList ++ (tl1.toList ++ eof1.toList)))))
          (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)
        obtain ⟨hrdk2, _, ck2, _, hrk2_l, hck2⟩ := readDottedKey_renderDottedKey hrk2 hok2.1.2
          (rem := '=' :: (wsR2.toList ++ (rv2.toList ++ ((rsuf2 ++ le2).toList ++ (tl2.toList ++ eof2.toList)))))
          (fun c r e => by obtain ⟨rfl, _⟩ := List.cons.inj e; decide)
        simp only [String.toList_append, List.append_assoc] at hrdk1 hrdk2
        have hd0 := congrArg (dropTrivia false) heq
        simp only [String.toList_append, List.append_assoc, show ("=" : String).toList = ['='] from rfl, List.cons_append, List.nil_append] at hd0
        rw [dropTrivia_closed_append false pre1.toList _ hok1.1.1 (fun c r e => by rw [hrk1_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact ⟨hck1.1, hck1.2.1, hck1.2.2.1⟩),
            dropTrivia_closed_append false pre2.toList _ hok2.1.1 (fun c r e => by rw [hrk2_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact ⟨hck2.1, hck2.2.1, hck2.2.2.1⟩)] at hd0
        have hrdk_eq := hrdk1.symm.trans ((congrArg readDottedKey hd0).trans hrdk2)
        injection hrdk_eq with hp; injection hp with hpath heq_part
        injection heq_part with _ hafter_eq
        obtain ⟨_, cv1, _, hrv1_l, hnd1, _⟩ := renderValueInline_head hrv1
        obtain ⟨_, cv2, _, hrv2_l, hnd2, _⟩ := renderValueInline_head hrv2
        have hd_eqr := congrArg dropHoriz hafter_eq
        rw [dropHoriz_append hok1.2 (fun c r e => by rw [hrv1_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact (not_triv_of_valHead hnd1).1),
            dropHoriz_append hok2.2 (fun c r e => by rw [hrv2_l, List.cons_append] at e; obtain ⟨rfl, _⟩ := List.cons.inj e; exact (not_triv_of_valHead hnd2).1)] at hd_eqr
        have hdt1 : ModelDelimTail ((rsuf1 ++ le1).toList ++ (tl1.toList ++ eof1.toList)) := lineSuffix_delimTail hsuf1 hle1
        have hdt2 : ModelDelimTail ((rsuf2 ++ le2).toList ++ (tl2.toList ++ eof2.toList)) := lineSuffix_delimTail hsuf2 hle2
        obtain ⟨heqv_v, hsuf_eq⟩ := renderValueInline_injective (sizeOf vt1) (Nat.le_refl _) hrv1 hrv2
          (by simpa [String.toList_append, List.append_assoc] using hdt1)
          (by simpa [String.toList_append, List.append_assoc] using hdt2) hd_eqr
        have htail_eq : tl1.toList ++ eof1.toList = tl2.toList ++ eof2.toList := by
          have hd := congrArg dropLineEnd hsuf_eq
          have h1' := (dropLineEnd_append (suf := suf1) (rsuf := rsuf1) (lineEnd := le1) hsuf1 hle1).1
          have h2' := (dropLineEnd_append (suf := suf2) (rsuf := rsuf2) (lineEnd := le2) hsuf2 hle2).1
          simp only [String.toList_append, List.append_assoc] at h1' h2'
          rwa [h1', h2'] at hd
        obtain ⟨rfl, hrel_n⟩ := insertAtActiveAndLookup_rel activePath dk1.path skel nsk1 nsk2
          e1 e2 v1 v2 hrel hins1 (hpath ▸ hins2) heqv_v
        have hwf_n := insertAtActiveAndLookup_wf activePath dk1.path skel nsk1 e1 v1 hwf hins1
        exact renderStmts_injective heof1_tr heof2_tr r1 r2 activePath nsk1 fsk1' fsk2' tl1 tl2
          (fun ht _ => heof1_nil ht) (fun ht _ => heof2_nil ht) hwf_n hrel_n htl1 htl2 htail_eq

/-- Standalone proof that `Toml.Model.render` is injective up to `TomlTableEquiv` (`Core.RenderInjectiveModulo`). -/
theorem render_injective_model : Core.RenderInjectiveModulo Model.render Model.TomlTableEquiv := by
  intro a b t1 t2 raw hr1 hr2
  have hr1' := hr1; have hr2' := hr2
  simp only [Model.render, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hr1' hr2'
  rcases hr1' with ⟨lf1, hlf1, rawCs1, hexp1, hraw1⟩
  rcases hr2' with ⟨lf2, hlf2, rawCs2, hexp2, hraw2⟩
  have hrawCs_eq : rawCs1 = rawCs2 := by
    have := congrArg String.toList (hraw1.trans hraw2.symm)
    simpa [String.toList_ofList] using this
  subst hrawCs_eq
  have hlf_cs_eq : lf1.toList = lf2.toList :=
    (stripCrBeforeLf_expandNewlines t1.crlfMask lf1.toList rawCs1 (noCr_renderLF hlf1) hexp1).symm.trans
    (stripCrBeforeLf_expandNewlines t2.crlfMask lf2.toList rawCs1 (noCr_renderLF hlf2) hexp2)
  unfold renderLF at hlf1 hlf2
  if hw1 : (!wellFormedTableBool a) = true then simp [hw1] at hlf1 else
  if hg1 : (!t1.stmts.isEmpty && !t1.trailingNewline && !t1.eofTrivia.isEmpty) = true then simp [hw1, hg1] at hlf1 else
  if he1 : (!isEofTrivia t1.eofTrivia) = true then simp [hw1, hg1, he1] at hlf1 else
  if hw2 : (!wellFormedTableBool b) = true then simp [hw2] at hlf2 else
  if hg2 : (!t2.stmts.isEmpty && !t2.trailingNewline && !t2.eofTrivia.isEmpty) = true then simp [hw2, hg2] at hlf2 else
  if he2 : (!isEofTrivia t2.eofTrivia) = true then simp [hw2, hg2, he2] at hlf2 else
  simp only [hw1, hg1, he1, hw2, hg2, he2, Bool.false_eq_true, ↓reduceIte,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hlf1 hlf2
  rcases hlf1 with ⟨⟨fsk1, body1⟩, hst1, hm1⟩
  rcases hlf2 with ⟨⟨fsk2, body2⟩, hst2, hm2⟩
  split at hm1 <;> try (simp at hm1; done)
  rename_i hncov1; injection hm1 with e1; subst e1
  split at hm2 <;> try (simp at hm2; done)
  rename_i hncov2; injection hm2 with e2; subst e2
  have heof1_ok : isEofTrivia t1.eofTrivia = true := by cases h : isEofTrivia t1.eofTrivia <;> simp_all
  have heof2_ok : isEofTrivia t2.eofTrivia = true := by cases h : isEofTrivia t2.eofTrivia <;> simp_all
  have hcov1 : skelMatchesEntries fsk1 a.toList = true := by cases h : skelMatchesEntries fsk1 a.toList <;> simp_all
  have hcov2 : skelMatchesEntries fsk2 b.toList = true := by cases h : skelMatchesEntries fsk2 b.toList <;> simp_all
  have hg1_imp : t1.trailingNewline = false → t1.stmts ≠ [] → t1.eofTrivia = "" := by
    intro htnl hne
    have hne_b : (!t1.stmts.isEmpty) = true := by cases hs : t1.stmts with | nil => exact absurd hs hne | cons _ _ => rfl
    cases he_b : t1.eofTrivia.isEmpty
    · exfalso; apply hg1; simp [hne_b, htnl, he_b]
    · exact String.isEmpty_iff.mp he_b
  have hg2_imp : t2.trailingNewline = false → t2.stmts ≠ [] → t2.eofTrivia = "" := by
    intro htnl hne
    have hne_b : (!t2.stmts.isEmpty) = true := by cases hs : t2.stmts with | nil => exact absurd hs hne | cons _ _ => rfl
    cases he_b : t2.eofTrivia.isEmpty
    · exfalso; apply hg2; simp [hne_b, htnl, he_b]
    · exact String.isEmpty_iff.mp he_b
  simp only [String.toList_append] at hlf_cs_eq
  obtain ⟨rfl, hrel_fin⟩ := renderStmts_injective heof1_ok heof2_ok t1.stmts t2.stmts [] [] fsk1 fsk2 body1 body2
    hg1_imp hg2_imp (by simp [skelEntriesWF]) (skelRel_nil _ _) hst1 hst2 hlf_cs_eq
  exact skelMatchesEntries_equiv fsk1 a.toList b.toList hcov1 hcov2 hrel_fin

end LeanSwe.Toml.Proofs

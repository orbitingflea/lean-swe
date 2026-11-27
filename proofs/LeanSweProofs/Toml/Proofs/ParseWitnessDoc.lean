import LeanSweProofs.Toml.Proofs.ParseWitnessHdr

/-!
# Document Parse-to-Render Completeness (`parseWithNum_ok_has_tape`)

Proves `parseDocumentFuel_witness` and `parseWithNum_ok_has_tape`, showing that every
string `raw` accepted by `parseWithNum` produces a `WellFormedTable` and a concrete
`RenderTape` rendering `parsed` back to `some raw`.
-/

namespace LeanSwe.Toml.Proofs

open LeanSwe.Toml
open LeanSwe.Toml.Model
open LeanSwe.Toml.Impl
open LeanSwe.NumParse

private theorem parseDocumentFuel_empty_cs (numApi : CharNumApi) (fuel : Nat)
    (activePath : List String) (root : List (String × Node)) :
    parseDocumentFuel numApi fuel [] activePath root = .ok root := by
  cases fuel <;> rfl

private theorem parseDocumentFuel_witness {numApi : NumParseApi} (hnum : ValidNumApi numApi) (fuel : Nat) :
    ∀ (cs : List Char) (activePath : List String) (root outRoot : List (String × Node)),
      CleanNorm cs →
      EntriesKeyNoDup root = true →
      ActivePathOpen activePath root →
      parseDocumentFuel (toCharNumApi numApi) fuel cs activePath root = .ok outRoot →
      EntriesKeyNoDup outRoot = true ∧
      EntriesExtend root outRoot ∧
      ∃ (stmts : List StmtTape) (tnl : Bool) (eof : String) (bodyStr : String),
        (!stmts.isEmpty && !tnl && !eof.isEmpty) = false ∧
        isEofTrivia eof = true ∧
        cs = (bodyStr ++ eof).toList ∧
        ∀ finalRoot, EntriesExtend outRoot finalRoot →
          renderStmts (entriesToTomlList finalRoot) activePath (entriesToSkel root) tnl stmts =
            some (entriesToSkel outRoot, bodyStr) := by
  induction fuel with
  | zero =>
    intro cs activePath root outRoot hcl hnd _ h
    unfold parseDocumentFuel at h
    cases hst : skipTriviaNewlines cs with
    | nil =>
      rw [hst] at h; obtain rfl := Except.ok.inj h
      have heof := skipTriviaNewlinesAux_eof_witness false cs hcl hst
      refine ⟨hnd, entriesExtend_refl root, [], true, String.ofList cs, "", rfl,
        by simpa [isEofTrivia, String.toList_ofList] using heof,
        by simp [String.toList_ofList], fun _ _ => rfl⟩
    | cons _ _ => rw [hst] at h; nomatch h
  | succ fuel ih =>
    intro cs activePath root outRoot hcl hnd hact h
    unfold parseDocumentFuel at h
    cases hst : skipTriviaNewlines cs with
    | nil =>
      rw [hst] at h; obtain rfl := Except.ok.inj h
      have heof := skipTriviaNewlinesAux_eof_witness false cs hcl hst
      refine ⟨hnd, entriesExtend_refl root, [], true, String.ofList cs, "", rfl,
        by simpa [isEofTrivia, String.toList_ofList] using heof,
        by simp [String.toList_ofList], fun _ _ => rfl⟩
    | cons c0 r0 =>
      rw [hst] at h
      obtain ⟨pre, hcs_pre, hpre_ok⟩ := skipTriviaNewlinesAux_cons_witness false cs hcl hst
      let preS := String.ofList pre
      have hpreS_ok : isClosedTrivia preS = true := by simpa [isClosedTrivia, preS, String.toList_ofList] using hpre_ok
      have hcl_cs1 := (cleanNorm_of_suffix hcl hcs_pre).2
      have finish_stmt : ∀ (stmt : StmtTape) (coreStr rsuf : String) (hasNl : Bool)
          (nextActive : List String) (nextRoot : List (String × Node)) (rEnd nextCs : List Char),
          EntriesKeyNoDup nextRoot = true →
          EntriesExtend root nextRoot →
          ActivePathOpen nextActive nextRoot →
          (if hasNl then rEnd = rsuf.toList ++ '\n' :: nextCs else nextCs = [] ∧ rEnd = rsuf.toList) →
          c0 :: r0 = coreStr.toList ++ rEnd →
          (∀ finalRoot tnl rest fsk tlStr,
            EntriesExtend nextRoot finalRoot →
            renderStmts (entriesToTomlList finalRoot) nextActive (entriesToSkel nextRoot) tnl rest = some (fsk, tlStr) →
            let le := if rest.isEmpty then (if tnl then "\n" else "") else "\n"
            renderStmts (entriesToTomlList finalRoot) activePath (entriesToSkel root) tnl (stmt :: rest) =
              some (fsk, preS ++ coreStr ++ rsuf ++ le ++ tlStr)) →
          parseDocumentFuel (toCharNumApi numApi) fuel nextCs nextActive nextRoot = .ok outRoot →
          EntriesKeyNoDup outRoot = true ∧ EntriesExtend root outRoot ∧
          ∃ stmts tnl eof bodyStr,
            (!stmts.isEmpty && !tnl && !eof.isEmpty) = false ∧
            isEofTrivia eof = true ∧
            cs = (bodyStr ++ eof).toList ∧
            ∀ finalRoot, EntriesExtend outRoot finalRoot →
              renderStmts (entriesToTomlList finalRoot) activePath (entriesToSkel root) tnl stmts =
                some (entriesToSkel outRoot, bodyStr) := by
        intro stmt coreStr rsuf hasNl nextActive nextRoot rEnd nextCs hnr_nd hnr_ext hnr_act hhasNl hc0_eq hmk hrec
        cases hasNl with
        | false =>
          rcases hhasNl with ⟨rfl, hrEnd⟩
          rw [parseDocumentFuel_empty_cs] at hrec; obtain rfl := Except.ok.inj hrec
          refine ⟨hnr_nd, hnr_ext, [stmt], false, "", preS ++ coreStr ++ rsuf, rfl, rfl, ?_, fun finalRoot hfin => ?_⟩
          · simp [hcs_pre, hc0_eq, hrEnd, preS, String.toList_append, String.toList_ofList, List.append_assoc]
          · simpa [String.append_empty] using hmk finalRoot false [] (entriesToSkel nextRoot) "" hfin rfl
        | true =>
          simp only [↓reduceIte] at hhasNl
          have hcl_next : CleanNorm nextCs := by
            have h1 := (cleanNorm_of_suffix hcl_cs1 hc0_eq).2
            rw [hhasNl] at h1
            exact (cleanNorm_cons.mp (cleanNorm_append.mp h1).2).2
          obtain ⟨hout_nd, hout_ext, stmtsT, tnlT, eofT, bodyT, hgT, heofT, hnext_eq, hrendT⟩ :=
            ih nextCs nextActive nextRoot outRoot hcl_next hnr_nd hnr_act hrec
          cases stmtsT with
          | nil =>
            have hnil := hrendT outRoot (entriesExtend_refl outRoot)
            simp only [renderStmts, Option.some.injEq, Prod.mk.injEq] at hnil
            rcases hnil with ⟨_, rfl⟩
            refine ⟨hout_nd, entriesExtend_trans hnr_ext hout_ext, [stmt], true, eofT,
              preS ++ coreStr ++ rsuf ++ "\n", rfl, heofT, ?_, fun finalRoot hfin => ?_⟩
            · simp [hcs_pre, hc0_eq, hhasNl, hnext_eq, preS, String.toList_append, String.toList_ofList, List.append_assoc]
            · simpa [String.append_empty] using
                hmk finalRoot true [] (entriesToSkel outRoot) "" (entriesExtend_trans hout_ext hfin) (hrendT finalRoot hfin)
          | cons s2 sr =>
            refine ⟨hout_nd, entriesExtend_trans hnr_ext hout_ext, stmt :: s2 :: sr, tnlT, eofT,
              preS ++ coreStr ++ rsuf ++ "\n" ++ bodyT, hgT, heofT, ?_, fun finalRoot hfin => ?_⟩
            · simp [hcs_pre, hc0_eq, hhasNl, hnext_eq, preS, String.toList_append, String.toList_ofList, List.append_assoc]
            · exact hmk finalRoot tnlT (s2 :: sr) (entriesToSkel outRoot) bodyT
                (entriesExtend_trans hout_ext hfin) (hrendT finalRoot hfin)
      by_cases hb1 : c0 = '['
      · subst hb1
        cases r0 with
        | nil =>
          simp [parseDottedKey, parseDottedKeyFuel, parseKeySegment, takeBareKeyChars, skipHorizWs, bind, Except.bind] at h
        | cons c1 r0' =>
          by_cases hb2 : c1 = '['
          · subst hb2
            split at h
            · nomatch ‹'[' :: _ = []›
            · rename_i r0'' heq_aot
              obtain ⟨_, hb2_eq⟩ := List.cons.inj heq_aot
              obtain ⟨_, rfl⟩ := List.cons.inj hb2_eq
              dsimp only [bind, Except.bind] at h
              have hcl_r0' := (cleanNorm_cons.mp (cleanNorm_cons.mp hcl_cs1).2).2
              obtain ⟨hr0'_eq, hwsO_ok⟩ := skipHorizWs_witness r0'
              have hcl_dk := (cleanNorm_of_suffix hcl_r0' hr0'_eq).2
              cases hdk : parseDottedKey (skipHorizWs r0') with
              | error _ => rw [hdk] at h; nomatch h
              | ok kp =>
                rcases kp with ⟨path, r1⟩; rw [hdk] at h; dsimp only at h
                obtain ⟨dk, rdk, wsTr, hdk_p, hrdk, hwsTr, hdk_eq⟩ := parseDottedKey_witness hcl_dk hdk
                have hcl_r1 := (cleanNorm_of_suffix hcl_dk hdk_eq).2
                obtain ⟨hr1_eq, hws1_ok⟩ := skipHorizWs_witness r1
                rcases hsw1 : skipHorizWs r1 with _ | ⟨cl1, _ | ⟨cl2, r2⟩⟩ <;> rw [hsw1] at h hr1_eq <;> try (simp at h; done)
                by_cases hcl_b1 : cl1 = ']'
                · subst hcl_b1
                  by_cases hcl_b2 : cl2 = ']'
                  · subst hcl_b2
                    split at h; rotate_left; · nomatch h
                    rename_i r2' heq_b2; obtain ⟨_, hb2⟩ := List.cons.inj heq_b2; obtain ⟨_, rfl⟩ := List.cons.inj hb2
                    have hcl_r2 := (cleanNorm_cons.mp (cleanNorm_cons.mp (cleanNorm_of_suffix hcl_r1 hr1_eq).2).2).2
                    cases hcse : consumeStatementEnd r2 with
                    | error _ => rw [hcse] at h; nomatch h
                    | ok nextCs =>
                      rw [hcse] at h; dsimp only at h
                      obtain ⟨suf, rsuf, hasNl, hrsuf, hhasNl⟩ := consumeStatementEnd_witness hcl_r2 hcse
                      cases hhdr : applyHeader .aot path root path with
                      | error _ => rw [hhdr] at h; nomatch h
                      | ok nextRoot =>
                        rw [hhdr] at h
                        obtain ⟨hnr_nd, hnr_ext, hnr_act, hnr_sk⟩ := applyHeader_witness .aot path path root nextRoot hnd hhdr
                        let wsOpen := String.ofList (takeHorizPrefix r0')
                        let wsClose := wsTr ++ String.ofList (takeHorizPrefix r1)
                        have hwsC_ok := isHorizWsStr_append hwsTr hws1_ok
                        refine finish_stmt (.aotHeader preS wsOpen dk wsClose suf)
                          ("[[" ++ wsOpen ++ rdk ++ wsClose ++ "]]") rsuf hasNl path nextRoot r2 nextCs
                          hnr_nd hnr_ext hnr_act hhasNl ?_ ?_ h
                        · conv => lhs; rw [hr0'_eq, hdk_eq, hr1_eq]
                          dsimp only [wsOpen, wsClose]
                          simp [String.toList_append, String.toList_ofList, List.append_assoc]
                        · intro finalRoot tnl rest fsk tlStr _ htl
                          have hsk' : applyHeaderSkel true (entriesToSkel root) dk.path = some (entriesToSkel nextRoot) := by
                            simpa [hdk_p, show (HeaderMode.aot == HeaderMode.aot) = true from rfl] using hnr_sk
                          have htl' : renderStmts (entriesToTomlList finalRoot) dk.path (entriesToSkel nextRoot) tnl rest = some (fsk, tlStr) := by
                            simpa [hdk_p] using htl
                          simp [renderStmts, preS, wsOpen, wsClose, hpreS_ok, hwsO_ok, hwsC_ok, hrdk, hrsuf, hsk', htl', String.append_assoc]
                  · split at h
                    · rename_i _ heq; exact absurd (List.cons.inj (List.cons.inj heq).2).1 hcl_b2
                    · cases h
                · split at h
                  · rename_i _ heq; exact absurd (List.cons.inj heq).1 hcl_b1
                  · cases h
            · rename_i rest hne heq
              obtain ⟨_, rfl⟩ := List.cons.inj heq
              exact False.elim (hne r0' rfl)
            · rename_i hne; exact False.elim (hne _ rfl)
          · split at h
            · nomatch ‹'[' :: _ = []›
            · rename_i rest heq; exact False.elim (hb2 (List.cons.inj (List.cons.inj heq).2).1)
            · rename_i rest _ heq; obtain ⟨_, rfl⟩ := List.cons.inj heq
              dsimp only [bind, Except.bind] at h
              have hcl_rest := (cleanNorm_cons.mp hcl_cs1).2
              obtain ⟨hrest_eq, hwsO_ok⟩ := skipHorizWs_witness (c1 :: r0')
              have hcl_dk := (cleanNorm_of_suffix hcl_rest hrest_eq).2
              cases hdk : parseDottedKey (skipHorizWs (c1 :: r0')) with
              | error _ => rw [hdk] at h; nomatch h
              | ok kp =>
                rcases kp with ⟨path, r1⟩; rw [hdk] at h; dsimp only at h
                obtain ⟨dk, rdk, wsTr, hdk_p, hrdk, hwsTr, hdk_eq⟩ := parseDottedKey_witness hcl_dk hdk
                have hcl_r1 := (cleanNorm_of_suffix hcl_dk hdk_eq).2
                obtain ⟨hr1_eq, hws1_ok⟩ := skipHorizWs_witness r1
                cases hsw1 : skipHorizWs r1 with
                | nil => rw [hsw1] at h; nomatch h
                | cons cl1 r2 =>
                  rw [hsw1] at h hr1_eq
                  by_cases hcl_b1 : cl1 = ']'
                  · subst hcl_b1
                    split at h; rotate_left; · nomatch h
                    rename_i r2' heq_b1; obtain ⟨_, rfl⟩ := List.cons.inj heq_b1
                    have hcl_r2 := (cleanNorm_cons.mp (cleanNorm_of_suffix hcl_r1 hr1_eq).2).2
                    cases hcse : consumeStatementEnd r2 with
                    | error _ => rw [hcse] at h; nomatch h
                    | ok nextCs =>
                      rw [hcse] at h; dsimp only at h
                      obtain ⟨suf, rsuf, hasNl, hrsuf, hhasNl⟩ := consumeStatementEnd_witness hcl_r2 hcse
                      cases hhdr : applyHeader .table path root path with
                      | error _ => rw [hhdr] at h; nomatch h
                      | ok nextRoot =>
                        rw [hhdr] at h
                        obtain ⟨hnr_nd, hnr_ext, hnr_act, hnr_sk⟩ := applyHeader_witness .table path path root nextRoot hnd hhdr
                        let wsOpen := String.ofList (takeHorizPrefix (c1 :: r0'))
                        let wsClose := wsTr ++ String.ofList (takeHorizPrefix r1)
                        have hwsC_ok := isHorizWsStr_append hwsTr hws1_ok
                        refine finish_stmt (.tableHeader preS wsOpen dk wsClose suf)
                          ("[" ++ wsOpen ++ rdk ++ wsClose ++ "]") rsuf hasNl path nextRoot r2 nextCs
                          hnr_nd hnr_ext hnr_act hhasNl ?_ ?_ h
                        · conv => lhs; rw [hrest_eq, hdk_eq, hr1_eq]
                          dsimp only [wsOpen, wsClose]
                          simp [String.toList_append, String.toList_ofList, List.append_assoc]
                        · intro finalRoot tnl rest fsk tlStr _ htl
                          have hsk' : applyHeaderSkel false (entriesToSkel root) dk.path = some (entriesToSkel nextRoot) := by
                            simpa [hdk_p, show (HeaderMode.table == HeaderMode.aot) = false from rfl] using hnr_sk
                          have htl' : renderStmts (entriesToTomlList finalRoot) dk.path (entriesToSkel nextRoot) tnl rest = some (fsk, tlStr) := by
                            simpa [hdk_p] using htl
                          simp [renderStmts, preS, wsOpen, wsClose, hpreS_ok, hwsO_ok, hwsC_ok, hrdk, hrsuf, hsk', htl', String.append_assoc]
                  · split at h
                    · rename_i _ heq; exact absurd (List.cons.inj heq).1 hcl_b1
                    · cases h
            · rename_i hne; exact False.elim (hne _ rfl)
      · split at h
        · nomatch ‹c0 :: r0 = []›
        · rename_i _ heq; exact False.elim (hb1 (List.cons.inj heq).1)
        · rename_i _ _ heq; exact False.elim (hb1 (List.cons.inj heq).1)
        · dsimp only [bind, Except.bind] at h
          cases hdk : parseDottedKey (c0 :: r0) with
          | error _ => rw [hdk] at h; nomatch h
          | ok kp =>
            rcases kp with ⟨relPath, r1⟩; rw [hdk] at h; dsimp only at h
            obtain ⟨dk, rdk, wsTr, hdk_p, hrdk, hwsTr, hdk_eq⟩ := parseDottedKey_witness hcl_cs1 hdk
            have hcl_r1 := (cleanNorm_of_suffix hcl_cs1 hdk_eq).2
            obtain ⟨hr1_eq, hws1_ok⟩ := skipHorizWs_witness r1
            cases hsw1 : skipHorizWs r1 with
            | nil => rw [hsw1] at h; nomatch h
            | cons cEq r2 =>
              rw [hsw1] at h hr1_eq
              by_cases heq_c : cEq = '='
              · subst heq_c
                split at h; rotate_left; · nomatch h
                rename_i r2' heq_eq; obtain ⟨_, rfl⟩ := List.cons.inj heq_eq
                have hcl_r2 := (cleanNorm_cons.mp (cleanNorm_of_suffix hcl_r1 hr1_eq).2).2
                obtain ⟨hr2_eq, hwsR_ok⟩ := skipHorizWs_witness r2
                have hcl_val := (cleanNorm_of_suffix hcl_r2 hr2_eq).2
                cases hpv : parseValue (toCharNumApi numApi) (skipHorizWs r2) with
                | error _ => rw [hpv] at h; nomatch h
                | ok vp =>
                  rcases vp with ⟨val, r3⟩; rw [hpv] at h; dsimp only at h
                  obtain ⟨vt, rv, hrv, hval_eq⟩ := parseValue_witness hnum hcl_val hpv
                  have hcl_r3 := (cleanNorm_of_suffix hcl_val hval_eq).2
                  cases hcse : consumeStatementEnd r3 with
                  | error _ => rw [hcse] at h; nomatch h
                  | ok nextCs =>
                    rw [hcse] at h; dsimp only at h
                    obtain ⟨suf, rsuf, hasNl, hrsuf, hhasNl⟩ := consumeStatementEnd_witness hcl_r3 hcse
                    cases hins : insertAtActivePath (activePath ++ relPath) root activePath relPath (valueToInlineNode val) with
                    | error _ => rw [hins] at h; nomatch h
                    | ok nextRoot =>
                      rw [hins] at h
                      obtain ⟨hnr_nd, hnr_ext, hnr_act, hnr_lu⟩ :=
                        insertAtActivePath_witness (activePath ++ relPath) relPath val activePath root nextRoot hnd hact hins
                      let wsEqL := wsTr ++ String.ofList (takeHorizPrefix r1)
                      let wsEqR := String.ofList (takeHorizPrefix r2)
                      have hwsL_ok := isHorizWsStr_append hwsTr hws1_ok
                      refine finish_stmt (.assign preS dk wsEqL wsEqR vt suf)
                        (rdk ++ wsEqL ++ "=" ++ wsEqR ++ rv) rsuf hasNl activePath nextRoot r3 nextCs
                        hnr_nd hnr_ext hnr_act hhasNl ?_ ?_ h
                      · conv => lhs; rw [hdk_eq, hr1_eq, hr2_eq, hval_eq]
                        dsimp only [wsEqL, wsEqR]
                        simp [String.toList_append, String.toList_ofList, List.append_assoc]
                      · intro finalRoot tnl rest fsk tlStr hfin htl
                        have hins_ok := hdk_p.symm ▸ hnr_lu finalRoot hfin
                        simp [renderStmts, preS, wsEqL, wsEqR, hpreS_ok, hwsL_ok, hwsR_ok, hrdk, hrsuf, hins_ok, hrv, htl, String.append_assoc]
              · split at h
                · rename_i _ heq; exact absurd (List.cons.inj heq).1 heq_c
                · cases h

/-- Every string accepted by `parseWithNum` produces a `WellFormedTable` and a concrete `RenderTape` rendering back to `raw`. -/
theorem parseWithNum_ok_has_tape (numApi : NumParseApi) (hnum : ValidNumApi numApi)
    (raw : String) (parsed : TomlTable)
    (hp : parseWithNum numApi raw = .ok parsed) :
    WellFormedTable parsed ∧ ∃ tape : RenderTape, Model.render parsed tape = some raw := by
  have hwf := parseWithNum_wellFormed numApi raw parsed hp
  refine ⟨hwf, ?_⟩
  unfold parseWithNum parseCharsWithNum at hp
  simp only [bind, Except.bind] at hp
  cases hnorm : normalizeChars 1 1 raw.toList with
  | error _ => rw [hnorm] at hp; nomatch hp
  | ok normCs =>
    rw [hnorm] at hp; dsimp only at hp
    obtain ⟨hcl_norm, hexp⟩ := normalizeChars_witness hnorm
    cases hdoc : parseDocumentFuel (toCharNumApi numApi) (normCs.length + 1) normCs [] [] with
    | error _ => rw [hdoc] at hp; nomatch hp
    | ok root =>
      rw [hdoc] at hp; obtain rfl := (Except.ok.inj hp).symm
      obtain ⟨hroot_nd, _, stmts, tnl, eof, bodyStr, hg, heof, hnorm_eq, hrend⟩ :=
        parseDocumentFuel_witness hnum (normCs.length + 1) normCs [] [] root hcl_norm entriesKeyNoDup_nil trivial hdoc
      let tape : RenderTape :=
        { stmts := stmts
        , trailingNewline := tnl
        , eofTrivia := eof
        , crlfMask := extractCrlfMask raw.toList }
      have hwf_b : wellFormedTableBool (entriesToTomlList root).toArray = true := hwf
      have hst_ok : renderStmts (entriesToTomlList root).toArray.toList [] [] tape.trailingNewline tape.stmts =
          some (entriesToSkel root, bodyStr) := by
        simpa [tape, entriesToSkel_nil] using hrend root (entriesExtend_refl root)
      have hcov : skelMatchesEntries (entriesToSkel root) (entriesToTomlList root).toArray.toList = true := by
        simpa using skelMatchesEntries_entriesToSkel root hroot_nd
      have hlf : renderLF (entriesToTomlList root).toArray tape = some (bodyStr ++ eof) := by
        simp [renderLF, tape, hwf_b, hg, heof, hst_ok, hcov]
      refine ⟨tape, ?_⟩
      rw [hnorm_eq, String.toList_append] at hexp
      simp [Model.render, hlf, tape, String.toList_append, hexp, String.ofList_toList]

end LeanSwe.Toml.Proofs

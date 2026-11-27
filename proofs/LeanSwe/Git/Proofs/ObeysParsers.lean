import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Model.Refines
import LeanSwe.Git.Proofs.ObeysBase

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open LeanSwe.Git
open LeanSwe.Git.Model

private theorem parsePorcelainStatusLoop_ok (revOut : List StatusEntry) (xs : List String)
    {entries : List StatusEntry}
    (hAcc : ∀ e ∈ revOut, !e.path.isEmpty = true)
    (h : parsePorcelainStatusLoop revOut xs = .ok entries) :
    ∀ e ∈ entries, !e.path.isEmpty = true := by
  match xs with
  | [] =>
    unfold parsePorcelainStatusLoop at h
    cases h
    intro e he
    exact hAcc e (List.mem_reverse.mp he)
  | recStr :: rest =>
    unfold parsePorcelainStatusLoop at h
    split at h
    · next x y pathChars _ =>
      split at h
      · cases h
      · next hOk =>
        have hPathNonEmpty : pathChars.isEmpty = false := by
          cases hp : pathChars.isEmpty
          · rfl
          · exfalso; exact hOk (by simp [hp])
        split at h
        · next ix wt =>
          split at h
          · cases rest with
            | nil => cases h
            | cons orig tail =>
              dsimp only at h
              apply parsePorcelainStatusLoop_ok _ tail _ h
              intro e he
              rcases List.mem_cons.mp he with rfl | hmem
              · exact not_isEmpty_ofList hPathNonEmpty
              · exact hAcc e hmem
          · apply parsePorcelainStatusLoop_ok _ rest _ h
            intro e he
            rcases List.mem_cons.mp he with rfl | hmem
            · exact not_isEmpty_ofList hPathNonEmpty
            · exact hAcc e hmem
        · cases h
    · cases h
termination_by xs.length

private theorem parsePorcelainStatusLoop_err (revOut : List StatusEntry) (xs : List String)
    {e : GitError}
    (h : parsePorcelainStatusLoop revOut xs = .error e) : e.message ≠ "" := by
  match xs with
  | [] => unfold parsePorcelainStatusLoop at h; cases h
  | recStr :: rest =>
    unfold parsePorcelainStatusLoop at h
    split at h
    · split at h
      · cases h; exact interp3_ne_empty _ _ _ (by decide)
      · split at h
        · split at h
          · cases rest with
            | nil => cases h; exact interp3_ne_empty _ _ _ (by decide)
            | cons orig tail => dsimp only at h; exact parsePorcelainStatusLoop_err _ tail h
          · exact parsePorcelainStatusLoop_err _ rest h
        · cases h; exact interp3_ne_empty _ _ _ (by decide)
    · cases h; exact interp3_ne_empty _ _ _ (by decide)
termination_by xs.length

/-- `Model.parsePorcelainStatusZ` guarantees non-empty paths on `.ok` and non-empty message on `.error`. -/
theorem parsePorcelainStatusZ_spec (bytes : ByteArray) :
    match parsePorcelainStatusZ bytes with
    | .ok entries => entries.all (fun e => !e.path.isEmpty) = true
    | .error e => e.message ≠ "" := by
  cases hRes : parsePorcelainStatusZ bytes with
  | ok entries =>
    unfold parsePorcelainStatusZ at hRes
    dsimp only [bind, Except.bind, pure, Except.pure] at hRes
    split at hRes
    · cases hRes; simp
    · cases hU : String.fromUTF8? bytes with
      | none => rw [hU] at hRes; cases hRes
      | some text =>
        rw [hU] at hRes; dsimp only at hRes
        cases hS : splitNulRecords text with
        | none => rw [hS] at hRes; cases hRes
        | some recs =>
          rw [hS] at hRes; dsimp only at hRes
          cases hL : parsePorcelainStatusLoop [] recs with
          | error _ => rw [hL] at hRes; cases hRes
          | ok xs =>
            rw [hL] at hRes; cases hRes
            have hAll := parsePorcelainStatusLoop_ok [] recs (fun _ h => nomatch h) hL
            simp only [Array.all_eq_true]
            intro i hi
            exact hAll xs[i] (List.getElem_mem _)
  | error e =>
    unfold parsePorcelainStatusZ at hRes
    dsimp only [bind, Except.bind, pure, Except.pure] at hRes
    split at hRes
    · cases hRes
    · cases hU : String.fromUTF8? bytes with
      | none => rw [hU] at hRes; cases hRes; decide
      | some text =>
        rw [hU] at hRes; dsimp only at hRes
        cases hS : splitNulRecords text with
        | none => rw [hS] at hRes; cases hRes; decide
        | some recs =>
          rw [hS] at hRes; dsimp only at hRes
          cases hL : parsePorcelainStatusLoop [] recs with
          | ok _ => rw [hL] at hRes; cases hRes
          | error e' =>
            rw [hL] at hRes; cases hRes
            exact parsePorcelainStatusLoop_err [] recs hL

private theorem parseDiffTokensLoop_err_nonEmpty (revOut : List DiffEntry) (xs : List String)
    {e : GitError} (h : parseDiffTokensLoop revOut xs = .error e) : e.message ≠ "" := by
  match xs with
  | [] => unfold parseDiffTokensLoop at h; cases h
  | tok :: rest =>
    unfold parseDiffTokensLoop at h
    split at h
    · cases rest with
      | nil => cases h; decide
      | cons path tail => dsimp only at h; exact parseDiffTokensLoop_err_nonEmpty _ tail h
    · cases rest with
      | nil => cases h; decide
      | cons path tail => dsimp only at h; exact parseDiffTokensLoop_err_nonEmpty _ tail h
    · cases rest with
      | nil => cases h; decide
      | cons path tail => dsimp only at h; exact parseDiffTokensLoop_err_nonEmpty _ tail h
    · cases rest with
      | nil => cases h; decide
      | cons path tail => dsimp only at h; exact parseDiffTokensLoop_err_nonEmpty _ tail h
    · cases rest with
      | nil => cases h; decide
      | cons path tail => dsimp only at h; exact parseDiffTokensLoop_err_nonEmpty _ tail h
    · split at h
      · next _ _ _ _ tail _ => exact parseDiffTokensLoop_err_nonEmpty _ tail h
      · cases h; exact interp3_ne_empty _ _ _ (by decide)
      · cases h; exact interp3_ne_empty _ _ _ (by decide)
    · split at h
      · next _ _ _ _ tail _ => exact parseDiffTokensLoop_err_nonEmpty _ tail h
      · cases h; exact interp3_ne_empty _ _ _ (by decide)
      · cases h; exact interp3_ne_empty _ _ _ (by decide)
    · cases h; exact interp3_ne_empty _ _ _ (by decide)
termination_by xs.length

/-- `Model.parseDiffNameStatusZ` errors always carry non-empty messages. -/
theorem parseDiffNameStatusZ_err_nonEmpty {bytes : ByteArray} {e : GitError}
    (h : parseDiffNameStatusZ bytes = .error e) : e.message ≠ "" := by
  unfold parseDiffNameStatusZ at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases hU : String.fromUTF8? bytes with
    | none => rw [hU] at h; cases h; decide
    | some text =>
      rw [hU] at h; dsimp only at h
      cases hS : splitNulRecords text with
      | none => rw [hS] at h; cases h; decide
      | some toks =>
        rw [hS] at h; dsimp only at h
        cases hl : parseDiffTokensLoop [] toks with
        | error e' =>
          rw [hl] at h; cases h
          exact parseDiffTokensLoop_err_nonEmpty [] toks hl
        | ok _ => rw [hl] at h; cases h

private theorem parseWorktreeAttrs_ok (info : WorktreeInfo) (headSeen : Bool) (lines : List String)
    {info' : WorktreeInfo} {hs' : Bool}
    (hInv : isValidWorktreeInfo info = true)
    (h : parseWorktreeAttrs info headSeen lines = .ok (info', hs')) :
    isValidWorktreeInfo info' = true := by
  induction lines generalizing info headSeen with
  | nil => unfold parseWorktreeAttrs at h; cases h; exact hInv
  | cons line rest ih =>
    unfold parseWorktreeAttrs at h
    dsimp only at h
    split at h
    · exact ih _ _ (by simpa [isValidWorktreeInfo] using hInv) h
    · split at h
      · exact ih _ _ (by simpa [isValidWorktreeInfo] using hInv) h
      · split at h
        · exact ih _ _ (by simpa [isValidWorktreeInfo] using hInv) h
        · split at h
          · exact ih _ _ (by simpa [isValidWorktreeInfo] using hInv) h
          · cases hH : stripPrefixChars ['H', 'E', 'A', 'D', ' '] line.toList with
            | some shaChars =>
              rw [hH] at h; dsimp only at h
              split at h
              · apply ih _ _ _ h
                simp only [isValidWorktreeInfo, Bool.and_eq_true, Option.all_none, and_true] at hInv ⊢
                exact ⟨hInv.1.1, hInv.2⟩
              · have hCid := mkCommitId_spec (String.ofList shaChars)
                cases hc : mkCommitId (String.ofList shaChars) with
                | error _ => rw [hc] at h; cases h
                | ok cid =>
                  rw [hc] at hCid h
                  apply ih _ _ _ h
                  simp only [isValidWorktreeInfo, Bool.and_eq_true] at hInv ⊢
                  exact ⟨⟨hInv.1.1, by simpa using hCid⟩, hInv.2⟩
            | none =>
              rw [hH] at h; dsimp only at h
              cases hB : stripPrefixChars ['b', 'r', 'a', 'n', 'c', 'h', ' '] line.toList with
              | some refChars =>
                rw [hB] at h; dsimp only at h
                cases hR : stripPrefixChars ['r', 'e', 'f', 's', '/', 'h', 'e', 'a', 'd', 's', '/'] refChars with
                | none => rw [hR] at h; cases h
                | some shortChars =>
                  rw [hR] at h; dsimp only at h
                  have hRef := mkRefName_spec (String.ofList shortChars)
                  cases hr : mkRefName (String.ofList shortChars) with
                  | error _ => rw [hr] at h; cases h
                  | ok ref =>
                    rw [hr] at hRef h
                    apply ih _ _ _ h
                    simp only [isValidWorktreeInfo, Bool.and_eq_true] at hInv ⊢
                    exact ⟨hInv.1, by simpa using hRef⟩
              | none =>
                rw [hB] at h; dsimp only at h
                cases hL : stripPrefixChars ['l', 'o', 'c', 'k', 'e', 'd', ' '] line.toList with
                | some _ => rw [hL] at h; exact ih _ _ (by simpa [isValidWorktreeInfo] using hInv) h
                | none =>
                  rw [hL] at h; dsimp only at h
                  cases hP : stripPrefixChars ['p', 'r', 'u', 'n', 'a', 'b', 'l', 'e', ' '] line.toList with
                  | some _ => rw [hP] at h; exact ih _ _ (by simpa [isValidWorktreeInfo] using hInv) h
                  | none => rw [hP] at h; exact ih _ _ hInv h

private theorem parseWorktreeAttrs_err (info : WorktreeInfo) (headSeen : Bool) (lines : List String)
    {e : GitError} (h : parseWorktreeAttrs info headSeen lines = .error e) : e.message ≠ "" := by
  induction lines generalizing info headSeen with
  | nil => unfold parseWorktreeAttrs at h; cases h
  | cons line rest ih =>
    unfold parseWorktreeAttrs at h
    dsimp only at h
    split at h
    · exact ih _ _ h
    · split at h
      · exact ih _ _ h
      · split at h
        · exact ih _ _ h
        · split at h
          · exact ih _ _ h
          · cases hH : stripPrefixChars ['H', 'E', 'A', 'D', ' '] line.toList with
            | some shaChars =>
              rw [hH] at h; dsimp only at h
              split at h
              · exact ih _ _ h
              · cases hc : mkCommitId (String.ofList shaChars) with
                | ok _ => rw [hc] at h; exact ih _ _ h
                | error _ => rw [hc] at h; cases h; exact interp3_ne_empty _ _ _ (by decide)
            | none =>
              rw [hH] at h; dsimp only at h
              cases hB : stripPrefixChars ['b', 'r', 'a', 'n', 'c', 'h', ' '] line.toList with
              | some refChars =>
                rw [hB] at h; dsimp only at h
                cases hR : stripPrefixChars ['r', 'e', 'f', 's', '/', 'h', 'e', 'a', 'd', 's', '/'] refChars with
                | none => rw [hR] at h; cases h; exact interp3_ne_empty _ _ _ (by decide)
                | some shortChars =>
                  rw [hR] at h; dsimp only at h
                  cases hr : mkRefName (String.ofList shortChars) with
                  | ok _ => rw [hr] at h; exact ih _ _ h
                  | error _ => rw [hr] at h; cases h; exact interp3_ne_empty _ _ _ (by decide)
              | none =>
                rw [hB] at h; dsimp only at h
                cases hL : stripPrefixChars ['l', 'o', 'c', 'k', 'e', 'd', ' '] line.toList with
                | some _ => rw [hL] at h; exact ih _ _ h
                | none =>
                  rw [hL] at h; dsimp only at h
                  cases hP : stripPrefixChars ['p', 'r', 'u', 'n', 'a', 'b', 'l', 'e', ' '] line.toList with
                  | some _ => rw [hP] at h; exact ih _ _ h
                  | none => rw [hP] at h; exact ih _ _ h

private theorem parseWorktreeStanza_ok {st : List String} {info : WorktreeInfo}
    (h : parseWorktreeStanza st = .ok info) : isValidWorktreeInfo info = true := by
  unfold parseWorktreeStanza at h
  cases st with
  | nil => cases h
  | cons header attrs =>
    dsimp only at h
    cases hW : stripPrefixChars ['w', 'o', 'r', 'k', 't', 'r', 'e', 'e', ' '] header.toList with
    | none => rw [hW] at h; cases h
    | some pathChars =>
      rw [hW] at h; dsimp only at h
      split at h
      · cases h
      · next hNe =>
        have hPath : pathChars.isEmpty = false := Bool.eq_false_iff.mpr hNe
        let base : WorktreeInfo := { path := String.ofList pathChars, head? := none, branch? := none }
        have hBase : isValidWorktreeInfo base = true := by
          simp only [base, isValidWorktreeInfo, Option.all_none, Bool.and_true]
          exact not_isEmpty_ofList hPath
        dsimp only [bind, Except.bind] at h
        cases ha : parseWorktreeAttrs base false attrs with
        | error _ => rw [ha] at h; cases h
        | ok pair =>
          rw [ha] at h; dsimp only at h
          split at h
          · cases h
          · cases h
            exact parseWorktreeAttrs_ok base false attrs hBase ha

private theorem parseWorktreeStanza_err {st : List String} {e : GitError}
    (h : parseWorktreeStanza st = .error e) : e.message ≠ "" := by
  unfold parseWorktreeStanza at h
  cases st with
  | nil => cases h; decide
  | cons header attrs =>
    dsimp only at h
    cases hW : stripPrefixChars ['w', 'o', 'r', 'k', 't', 'r', 'e', 'e', ' '] header.toList with
    | none => rw [hW] at h; cases h; exact interp3_ne_empty _ _ _ (by decide)
    | some pathChars =>
      rw [hW] at h; dsimp only at h
      split at h
      · cases h; decide
      · dsimp only [bind, Except.bind] at h
        let base : WorktreeInfo := { path := String.ofList pathChars, head? := none, branch? := none }
        cases ha : parseWorktreeAttrs base false attrs with
        | error e' =>
          rw [ha] at h; cases h
          exact parseWorktreeAttrs_err base false attrs ha
        | ok pair =>
          rw [ha] at h; dsimp only at h
          split at h
          · cases h; exact interp3_ne_empty _ _ _ (by decide)
          · cases h

private theorem parseWorktreeStanzasLoop_ok (revOut : List WorktreeInfo) (xs : List (List String))
    {infos : List WorktreeInfo}
    (hAcc : ∀ w ∈ revOut, isValidWorktreeInfo w = true)
    (h : parseWorktreeStanzasLoop revOut xs = .ok infos) :
    ∀ w ∈ infos, isValidWorktreeInfo w = true := by
  induction xs generalizing revOut with
  | nil =>
    unfold parseWorktreeStanzasLoop at h
    cases h
    intro w hw
    exact hAcc w (List.mem_reverse.mp hw)
  | cons st rest ih =>
    unfold parseWorktreeStanzasLoop at h
    cases hs : parseWorktreeStanza st with
    | error _ => rw [hs] at h; cases h
    | ok info =>
      rw [hs] at h
      apply ih _ _ h
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hmem
      · exact parseWorktreeStanza_ok hs
      · exact hAcc w hmem

private theorem parseWorktreeStanzasLoop_err (revOut : List WorktreeInfo) (xs : List (List String))
    {e : GitError} (h : parseWorktreeStanzasLoop revOut xs = .error e) : e.message ≠ "" := by
  induction xs generalizing revOut with
  | nil => unfold parseWorktreeStanzasLoop at h; cases h
  | cons st rest ih =>
    unfold parseWorktreeStanzasLoop at h
    cases hs : parseWorktreeStanza st with
    | error e' => rw [hs] at h; cases h; exact parseWorktreeStanza_err hs
    | ok info => rw [hs] at h; exact ih _ h

/-- `Model.parseWorktreeListPorcelain` guarantees `isValidWorktreeInfo` on `.ok` and non-empty message on `.error`. -/
theorem parseWorktreeListPorcelain_spec (bytes : ByteArray) :
    match parseWorktreeListPorcelain bytes with
    | .ok infos => infos.all isValidWorktreeInfo = true
    | .error e => e.message ≠ "" := by
  cases hRes : parseWorktreeListPorcelain bytes with
  | ok infos =>
    unfold parseWorktreeListPorcelain at hRes
    dsimp only [bind, Except.bind, pure, Except.pure] at hRes
    split at hRes
    · cases hRes; simp
    · cases hU : String.fromUTF8? bytes with
      | none => rw [hU] at hRes; cases hRes
      | some text =>
        rw [hU] at hRes; dsimp only at hRes
        cases hT : splitNulTokensAllowEmptyLoop [] [] text.toList with
        | none => rw [hT] at hRes; cases hRes
        | some toks =>
          rw [hT] at hRes; dsimp only at hRes
          cases hS : splitWorktreeStanzasLoop [] [] toks with
          | none => rw [hS] at hRes; cases hRes
          | some stanzas =>
            rw [hS] at hRes; dsimp only at hRes
            cases hL : parseWorktreeStanzasLoop [] stanzas with
            | error _ => rw [hL] at hRes; cases hRes
            | ok xs =>
              rw [hL] at hRes; cases hRes
              have hAll := parseWorktreeStanzasLoop_ok [] stanzas (fun _ h => nomatch h) hL
              simp only [Array.all_eq_true]
              intro i hi
              exact hAll xs[i] (List.getElem_mem _)
  | error e =>
    unfold parseWorktreeListPorcelain at hRes
    dsimp only [bind, Except.bind, pure, Except.pure] at hRes
    split at hRes
    · cases hRes
    · cases hU : String.fromUTF8? bytes with
      | none => rw [hU] at hRes; cases hRes; decide
      | some text =>
        rw [hU] at hRes; dsimp only at hRes
        cases hT : splitNulTokensAllowEmptyLoop [] [] text.toList with
        | none => rw [hT] at hRes; cases hRes; decide
        | some toks =>
          rw [hT] at hRes; dsimp only at hRes
          cases hS : splitWorktreeStanzasLoop [] [] toks with
          | none => rw [hS] at hRes; cases hRes; decide
          | some stanzas =>
            rw [hS] at hRes; dsimp only at hRes
            cases hL : parseWorktreeStanzasLoop [] stanzas with
            | ok _ => rw [hL] at hRes; cases hRes
            | error e' =>
              rw [hL] at hRes; cases hRes
              exact parseWorktreeStanzasLoop_err [] stanzas hL

end LeanSwe.Git.Proofs

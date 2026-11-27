import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.SpecTests

set_option Elab.async false

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

private instance : LawfulBEq CommitId where
  eq_of_beq {a b} h := by
    cases a with | mk ha =>
    cases b with | mk hb =>
    have h' : (ha == hb) = true := h
    exact congrArg CommitId.mk (beq_iff_eq.mp h')
  rfl {a} := by
    cases a with | mk ha =>
    change (ha == ha) = true
    exact beq_self_eq_true ha

private instance : LawfulBEq RefName where
  eq_of_beq {a b} h := by
    cases a with | mk ra =>
    cases b with | mk rb =>
    have h' : (ra == rb) = true := h
    exact congrArg RefName.mk (beq_iff_eq.mp h')
  rfl {a} := by
    cases a with | mk ra =>
    change (ra == ra) = true
    exact beq_self_eq_true ra

private theorem fromUTF8_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?, String.toUTF8, s.isValidUTF8]

private theorem toUTF8_eq_empty_iff (s : String) : s.toUTF8.isEmpty = true ↔ s = "" := by
  change (s.toByteArray.size == 0) = true ↔ s = ""
  rw [beq_iff_eq]
  exact String.utf8ByteSize_eq_zero_iff

private theorem hasNulChar_eq_false_iff {cs : List Char} :
    hasNulChar cs = false ↔ ∀ c ∈ cs, c ≠ Char.ofNat 0 := by
  induction cs with
  | nil => simp [hasNulChar]
  | cons c cs ih =>
    simp [hasNulChar, ih]

private theorem string_ofList_append (xs ys : List Char) :
    String.ofList (xs ++ ys) = String.ofList xs ++ String.ofList ys :=
  String.toList_injective (by simp)

/-- Shared proof helper `decodeUtf8Lossy_toUTF8`. -/
theorem decodeUtf8Lossy_toUTF8 (s : String) :
    Impl.decodeUtf8Lossy s.toUTF8 = s := by
  unfold Impl.decodeUtf8Lossy
  rw [fromUTF8_toUTF8]

/-- Shared proof helper `decodeUtf8Checked_toUTF8`. -/
theorem decodeUtf8Checked_toUTF8 (s : String) :
    Impl.decodeUtf8Checked s.toUTF8 = .ok s := by
  unfold Impl.decodeUtf8Checked
  rw [fromUTF8_toUTF8]

/-- Shared proof helper `all_no_nul_of_list`. -/
theorem all_no_nul_of_list (xs : List String)
    (h : xs.all (fun a => !hasNulChar a.toList) = true) :
    (xs.toArray.all fun a => !hasNulChar a.toList) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hmem : xs.toArray[i] ∈ xs := by simp
  exact List.all_eq_true.mp h _ hmem

theorem hasNulCharImpl_eq (cs : List Char) :
    Impl.hasNulCharImpl cs = hasNulChar cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp only [Impl.hasNulCharImpl, hasNulChar, ih]

theorem hasInvalidEnvKeyCharImpl_eq (cs : List Char) :
    Impl.hasInvalidEnvKeyCharImpl cs = hasInvalidEnvKeyChar cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp only [Impl.hasInvalidEnvKeyCharImpl, hasInvalidEnvKeyChar, ih]

theorem isValidEnvKeyImpl_eq (k : String) :
    Impl.isValidEnvKeyImpl k = isValidEnvKey k := by
  unfold Impl.isValidEnvKeyImpl isValidEnvKey
  rw [hasInvalidEnvKeyCharImpl_eq]

theorem isValidEnvValImpl_eq (v? : Option String) :
    Impl.isValidEnvValImpl? v? = isValidEnvVal? v? := by
  cases v? with
  | none => rfl
  | some v => simp only [Impl.isValidEnvValImpl?, isValidEnvVal?, hasNulCharImpl_eq]

theorem cleanGitEnvImpl_eq (inheritedEnv : Array (String × String))
    (extraEnv : Array (String × Option String) := #[]) :
    Impl.cleanGitEnvImpl inheritedEnv extraEnv = cleanGitEnv inheritedEnv extraEnv := by
  unfold Impl.cleanGitEnvImpl cleanGitEnv
  simp only [isValidEnvKeyImpl_eq, isValidEnvValImpl_eq]
  rfl

theorem isValidPathArgImpl_eq (s : String) :
    Impl.isValidPathArgImpl s = isValidPathArg s := by
  unfold Impl.isValidPathArgImpl isValidPathArg
  dsimp only
  rw [hasNulCharImpl_eq]

theorem validateFsPathArgImpl_eq (p : String) :
    Impl.validateFsPathArgImpl p = validateFsPathArg p := by
  unfold Impl.validateFsPathArgImpl validateFsPathArg
  rw [isValidPathArgImpl_eq]

theorem validateCloneEndpointImpl_eq (p : String) :
    Impl.validateCloneEndpointImpl p = validateCloneEndpoint p := by
  unfold Impl.validateCloneEndpointImpl validateCloneEndpoint
  rw [isValidPathArgImpl_eq]

theorem validateRelRepoPathImpl_eq (p : String) :
    Impl.validateRelRepoPathImpl p = validateRelRepoPath p := by
  unfold Impl.validateRelRepoPathImpl validateRelRepoPath
  rw [isValidPathArgImpl_eq]

theorem validateCommitOptionsImpl_eq (opts : CommitOptions) :
    Impl.validateCommitOptionsImpl opts = validateCommitOptions opts := by
  unfold Impl.validateCommitOptionsImpl validateCommitOptions
  simp only [hasNulCharImpl_eq]
  rfl

theorem startsWithCharsImpl_eq : ∀ (ps cs : List Char), Impl.startsWithCharsImpl ps cs = startsWithChars ps cs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, c :: cs => by simp only [Impl.startsWithCharsImpl, startsWithChars, startsWithCharsImpl_eq ps cs]

theorem hasSubstrCharsImpl_eq (needle : List Char) :
    ∀ (hay : List Char), Impl.hasSubstrCharsImpl needle hay = hasSubstrChars needle hay
  | [] => rfl
  | c :: cs => by
    simp only [Impl.hasSubstrCharsImpl, hasSubstrChars, startsWithCharsImpl_eq, hasSubstrCharsImpl_eq needle cs]

theorem endsWithCharsImpl_eq (suf cs : List Char) :
    Impl.endsWithCharsImpl suf cs = endsWithChars suf cs :=
  startsWithCharsImpl_eq suf.reverse cs.reverse

theorem splitSlashLoopImpl_eq (cur : List Char) (revSegs : List (List Char)) (cs : List Char) :
    Impl.splitSlashLoopImpl cur revSegs cs = splitSlashLoop cur revSegs cs := by
  induction cs generalizing cur revSegs with
  | nil => rfl
  | cons c rest ih =>
    unfold Impl.splitSlashLoopImpl splitSlashLoop
    split
    · exact ih [] (cur.reverse :: revSegs)
    · exact ih (c :: cur) revSegs

theorem isValidRefNameStrImpl_eq (s : String) :
    Impl.isValidRefNameStrImpl s = isValidRefNameStr s := by
  unfold Impl.isValidRefNameStrImpl isValidRefNameStr Impl.splitSlashCharsImpl splitSlashChars
    Impl.isValidRefComponentImpl isValidRefComponent
  simp only [endsWithCharsImpl_eq, hasSubstrCharsImpl_eq, splitSlashLoopImpl_eq]
  rfl

theorem mkRefNameImpl_eq (s : String) :
    Impl.mkRefNameImpl s = mkRefName s := by
  unfold Impl.mkRefNameImpl mkRefName
  rw [isValidRefNameStrImpl_eq]

theorem isValidCommitIdStrImpl_eq (s : String) :
    Impl.isValidCommitIdStrImpl s = isValidCommitIdStr s := rfl

theorem mkCommitIdImpl_eq (s : String) :
    Impl.mkCommitIdImpl s = mkCommitId s := rfl

theorem isValidRevSpecImpl_eq (s : String) :
    Impl.isValidRevSpecImpl s = isValidRevSpec s := rfl

theorem isValidStrictRevSpecImpl_eq (s : String) :
    Impl.isValidStrictRevSpecImpl s = isValidStrictRevSpec s := by
  unfold Impl.isValidStrictRevSpecImpl isValidStrictRevSpec
  simp only [hasSubstrCharsImpl_eq]
  rfl

theorem isValidRemoteOrRefspecImpl_eq (s : String) :
    Impl.isValidRemoteOrRefspecImpl s = isValidRemoteOrRefspec s := rfl

theorem parseNatDigitsAuxImpl_eq (acc : Nat) (cs : List Char) :
    Impl.parseNatDigitsAuxImpl acc cs = parseNatDigitsAux acc cs := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c rest ih =>
    unfold Impl.parseNatDigitsAuxImpl parseNatDigitsAux
    split
    · exact ih _
    · rfl

theorem splitNulRecordsLoopImpl_eq (acc : List Char) (revOut : List String) (cs : List Char) :
    Impl.splitNulRecordsLoopImpl acc revOut cs = splitNulRecordsLoop acc revOut cs := by
  induction cs generalizing acc revOut with
  | nil => rfl
  | cons c rest ih =>
    unfold Impl.splitNulRecordsLoopImpl splitNulRecordsLoop
    split
    · split
      · rfl
      · exact ih [] (String.ofList acc.reverse :: revOut)
    · exact ih (c :: acc) revOut

theorem parsePorcelainStatusLoopImpl_eq (revOut : List StatusEntry) (xs : List String) :
    Impl.parsePorcelainStatusLoopImpl revOut xs = parsePorcelainStatusLoop revOut xs := by
  match xs with
  | [] => rfl
  | recStr :: rest =>
    unfold Impl.parsePorcelainStatusLoopImpl parsePorcelainStatusLoop
    generalize recStr.toList = cs
    cases cs with
    | nil => rfl
    | cons x r1 =>
      cases r1 with
      | nil => rfl
      | cons y r2 =>
        cases r2 with
        | nil => rfl
        | cons c pathChars =>
          by_cases hc : c = ' '
          · subst hc
            simp only
            by_cases hBad : (pathChars.isEmpty || !isValidStatusPair x y) = true
            · simp only [show Impl.isValidStatusPairImpl x y = isValidStatusPair x y from rfl, hBad, ↓reduceIte]
            · simp only [show Impl.isValidStatusPairImpl x y = isValidStatusPair x y from rfl, hBad, Bool.false_eq_true, ↓reduceIte,
                show Impl.statusCharToKindImpl? x = statusCharToKind? x from rfl,
                show Impl.statusCharToKindImpl? y = statusCharToKind? y from rfl]
              cases statusCharToKind? x with
              | none => rfl
              | some ix =>
                cases statusCharToKind? y with
                | none => rfl
                | some wt =>
                  dsimp only
                  by_cases hRC : (x == 'R' || x == 'C' || y == 'R' || y == 'C') = true
                  · simp only [hRC, ↓reduceIte]
                    cases rest with
                    | nil => rfl
                    | cons orig tail => exact parsePorcelainStatusLoopImpl_eq _ tail
                  · simp only [hRC, Bool.false_eq_true, ↓reduceIte]
                    exact parsePorcelainStatusLoopImpl_eq _ rest
          · split
            · simp_all
            · split <;> simp_all
termination_by xs.length

theorem parsePorcelainStatusZImpl_eq (bytes : ByteArray) :
    Impl.parsePorcelainStatusZImpl bytes = parsePorcelainStatusZ bytes := by
  unfold Impl.parsePorcelainStatusZImpl parsePorcelainStatusZ Impl.splitNulRecordsImpl splitNulRecords
  simp only [splitNulRecordsLoopImpl_eq, parsePorcelainStatusLoopImpl_eq]
  rfl

theorem parseDiffTokensLoopImpl_eq (revOut : List DiffEntry) (xs : List String) :
    Impl.parseDiffTokensLoopImpl revOut xs = parseDiffTokensLoop revOut xs := by
  match xs with
  | [] => rfl
  | tok :: rest =>
    unfold Impl.parseDiffTokensLoopImpl parseDiffTokensLoop
    generalize tok.toList = cs
    cases cs with
    | nil => rfl
    | cons c scoreChars =>
      by_cases h1 : (c = 'A' ∨ c = 'M' ∨ c = 'D' ∨ c = 'T' ∨ c = 'U') ∧ scoreChars = []
      · rcases h1 with ⟨hc, rfl⟩
        rcases hc with rfl | rfl | rfl | rfl | rfl <;>
          (cases rest with
           | nil => rfl
           | cons _ tail => exact parseDiffTokensLoopImpl_eq _ tail)
      · by_cases h2 : c = 'R' ∨ c = 'C'
        · rcases h2 with rfl | rfl <;> (
            simp only [Impl.parseSimilarityScoreImpl, parseSimilarityScore, parseNatDigitsAuxImpl_eq]
            cases (if scoreChars.isEmpty then some 100 else parseNatDigitsAux 0 scoreChars) with
            | none => rfl
            | some _ =>
              cases rest with
              | nil => rfl
              | cons _ rest2 =>
                cases rest2 with
                | nil => rfl
                | cons _ tail => exact parseDiffTokensLoopImpl_eq _ tail)
        · split <;> simp_all
termination_by xs.length

theorem parseDiffNameStatusZImpl_eq (bytes : ByteArray) :
    Impl.parseDiffNameStatusZImpl bytes = parseDiffNameStatusZ bytes := by
  unfold Impl.parseDiffNameStatusZImpl parseDiffNameStatusZ Impl.splitNulRecordsImpl splitNulRecords
  simp only [splitNulRecordsLoopImpl_eq, parseDiffTokensLoopImpl_eq]
  rfl

theorem splitNulTokensAllowEmptyLoopImpl_eq (acc : List Char) (revOut : List String) (cs : List Char) :
    Impl.splitNulTokensAllowEmptyLoopImpl acc revOut cs = splitNulTokensAllowEmptyLoop acc revOut cs := by
  induction cs generalizing acc revOut with
  | nil => rfl
  | cons c rest ih =>
    unfold Impl.splitNulTokensAllowEmptyLoopImpl splitNulTokensAllowEmptyLoop
    split
    · exact ih [] (String.ofList acc.reverse :: revOut)
    · exact ih (c :: acc) revOut

theorem splitWorktreeStanzasLoopImpl_eq (cur : List String) (revOut : List (List String)) (xs : List String) :
    Impl.splitWorktreeStanzasLoopImpl cur revOut xs = splitWorktreeStanzasLoop cur revOut xs := by
  induction xs generalizing cur revOut with
  | nil => rfl
  | cons tok rest ih =>
    by_cases hEmp : tok = ""
    · subst hEmp
      simp only [Impl.splitWorktreeStanzasLoopImpl, splitWorktreeStanzasLoop]
      by_cases hCur : cur.isEmpty = true
      · simp only [hCur, ↓reduceIte]
      · simp only [hCur, Bool.false_eq_true, ↓reduceIte]
        exact ih [] (cur.reverse :: revOut)
    · have h1 : Impl.splitWorktreeStanzasLoopImpl cur revOut (tok :: rest) =
          Impl.splitWorktreeStanzasLoopImpl (tok :: cur) revOut rest := by
        conv => lhs; rw [Impl.splitWorktreeStanzasLoopImpl.eq_def]
        split
        · contradiction
        · rename_i heq; cases heq; contradiction
        · rename_i heq; cases heq; rfl
      have h2 : splitWorktreeStanzasLoop cur revOut (tok :: rest) =
          splitWorktreeStanzasLoop (tok :: cur) revOut rest := by
        conv => lhs; rw [splitWorktreeStanzasLoop.eq_def]
        split
        · contradiction
        · rename_i heq; cases heq; contradiction
        · rename_i heq; cases heq; rfl
      rw [h1, h2]
      exact ih (tok :: cur) revOut

theorem stripPrefixCharsImpl_eq : ∀ (ps cs : List Char), Impl.stripPrefixCharsImpl ps cs = stripPrefixChars ps cs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, c :: cs => by simp only [Impl.stripPrefixCharsImpl, stripPrefixChars, stripPrefixCharsImpl_eq ps cs]

theorem parseWorktreeAttrsImpl_eq (info : WorktreeInfo) (headSeen : Bool) (lines : List String) :
    Impl.parseWorktreeAttrsImpl info headSeen lines = parseWorktreeAttrs info headSeen lines := by
  induction lines generalizing info headSeen with
  | nil => rfl
  | cons line rest ih =>
    unfold Impl.parseWorktreeAttrsImpl parseWorktreeAttrs
    simp only [stripPrefixCharsImpl_eq, mkRefNameImpl_eq, mkCommitIdImpl_eq,
      show ∀ s, Impl.isAllZerosCommitStrImpl s = isAllZerosCommitStr s from fun _ => rfl]
    split
    · exact ih _ _
    · split
      · exact ih _ _
      · split
        · exact ih _ _
        · split
          · exact ih _ _
          · cases stripPrefixChars ['H', 'E', 'A', 'D', ' '] line.toList with
            | some shaChars =>
              dsimp only
              split
              · exact ih _ _
              · cases mkCommitId (String.ofList shaChars) with
                | ok _ => exact ih _ _
                | error _ => rfl
            | none =>
              dsimp only
              cases stripPrefixChars ['b', 'r', 'a', 'n', 'c', 'h', ' '] line.toList with
              | some refChars =>
                dsimp only
                cases stripPrefixChars ['r', 'e', 'f', 's', '/', 'h', 'e', 'a', 'd', 's', '/'] refChars with
                | some shortChars =>
                  dsimp only
                  cases mkRefName (String.ofList shortChars) with
                  | ok _ => exact ih _ _
                  | error _ => rfl
                | none => rfl
              | none =>
                dsimp only
                cases stripPrefixChars ['l', 'o', 'c', 'k', 'e', 'd', ' '] line.toList with
                | some _ => exact ih _ _
                | none =>
                  dsimp only
                  cases stripPrefixChars ['p', 'r', 'u', 'n', 'a', 'b', 'l', 'e', ' '] line.toList with
                  | some _ => exact ih _ _
                  | none => exact ih _ _

theorem parseWorktreeStanzaImpl_eq (xs : List String) :
    Impl.parseWorktreeStanzaImpl xs = parseWorktreeStanza xs := by
  unfold Impl.parseWorktreeStanzaImpl parseWorktreeStanza
  cases xs with
  | nil => rfl
  | cons header attrs =>
    simp only [stripPrefixCharsImpl_eq, parseWorktreeAttrsImpl_eq]
    rfl

theorem parseWorktreeStanzasLoopImpl_eq (revOut : List WorktreeInfo) (xs : List (List String)) :
    Impl.parseWorktreeStanzasLoopImpl revOut xs = parseWorktreeStanzasLoop revOut xs := by
  induction xs generalizing revOut with
  | nil => rfl
  | cons st rest ih =>
    unfold Impl.parseWorktreeStanzasLoopImpl parseWorktreeStanzasLoop
    rw [parseWorktreeStanzaImpl_eq]
    cases parseWorktreeStanza st with
    | ok info => exact ih (info :: revOut)
    | error _ => rfl

theorem parseWorktreeListPorcelainImpl_eq (bytes : ByteArray) :
    Impl.parseWorktreeListPorcelainImpl bytes = parseWorktreeListPorcelain bytes := by
  unfold Impl.parseWorktreeListPorcelainImpl parseWorktreeListPorcelain
  simp only [splitNulTokensAllowEmptyLoopImpl_eq, splitWorktreeStanzasLoopImpl_eq, parseWorktreeStanzasLoopImpl_eq]
  rfl

private def splitNulRecordsSpec (acc : List Char) : List Char → Option (List String)
  | [] => if acc.isEmpty then some [] else none
  | c :: cs =>
    if c == Char.ofNat 0 then
      if acc.isEmpty then none
      else (splitNulRecordsSpec [] cs).map (String.ofList acc.reverse :: ·)
    else
      splitNulRecordsSpec (c :: acc) cs

private def splitNulTokensAllowEmptySpec (acc : List Char) : List Char → Option (List String)
  | [] => if acc.isEmpty then some [] else none
  | c :: cs =>
    if c == Char.ofNat 0 then
      (splitNulTokensAllowEmptySpec [] cs).map (String.ofList acc.reverse :: ·)
    else
      splitNulTokensAllowEmptySpec (c :: acc) cs

private def splitWorktreeStanzasSpec (cur : List String) : List String → Option (List (List String))
  | [] => if cur.isEmpty then some [] else none
  | "" :: rest =>
    if cur.isEmpty then none
    else (splitWorktreeStanzasSpec [] rest).map (cur.reverse :: ·)
  | tok :: rest => splitWorktreeStanzasSpec (tok :: cur) rest

private def parseWorktreeStanzasSpec : List (List String) → Except GitError (List WorktreeInfo)
  | [] => .ok []
  | st :: rest => do
    let info ← parseWorktreeStanza st
    let tail ← parseWorktreeStanzasSpec rest
    .ok (info :: tail)

private def parsePorcelainStatusSpec : List String → Except GitError (List StatusEntry)
  | [] => .ok []
  | recStr :: rest =>
    match recStr.toList with
    | x :: y :: ' ' :: pathChars =>
      if pathChars.isEmpty || !isValidStatusPair x y then
        .error { kind := .parseError, message := s!"invalid porcelain status entry: '{recStr}'" }
      else
        match statusCharToKind? x, statusCharToKind? y with
        | some ix, some wt =>
          let path := String.ofList pathChars
          if x == 'R' || x == 'C' || y == 'R' || y == 'C' then
            match rest with
            | [] =>
              .error { kind := .parseError, message := s!"truncated rename/copy status entry for '{path}'" }
            | orig :: tail =>
              (parsePorcelainStatusSpec tail).map
                ({ indexStatus := ix, worktreeStatus := wt, path := path, origPath := some orig } :: ·)
          else
            (parsePorcelainStatusSpec rest).map
              ({ indexStatus := ix, worktreeStatus := wt, path := path, origPath := none } :: ·)
        | _, _ =>
          .error { kind := .parseError, message := s!"invalid status characters in '{recStr}'" }
    | _ =>
      .error { kind := .parseError, message := s!"malformed porcelain status record: '{recStr}'" }

private def parseDiffTokensSpec : List String → Except GitError (List DiffEntry)
  | [] => .ok []
  | tok :: rest =>
    match tok.toList with
    | ['A'] =>
      match rest with
      | path :: tail => (parseDiffTokensSpec tail).map ({ kind := .added, path := path } :: ·)
      | [] => .error { kind := .parseError, message := "truncated A entry in git diff -z" }
    | ['M'] =>
      match rest with
      | path :: tail => (parseDiffTokensSpec tail).map ({ kind := .modified, path := path } :: ·)
      | [] => .error { kind := .parseError, message := "truncated M entry in git diff -z" }
    | ['D'] =>
      match rest with
      | path :: tail => (parseDiffTokensSpec tail).map ({ kind := .deleted, path := path } :: ·)
      | [] => .error { kind := .parseError, message := "truncated D entry in git diff -z" }
    | ['T'] =>
      match rest with
      | path :: tail => (parseDiffTokensSpec tail).map ({ kind := .typeChanged, path := path } :: ·)
      | [] => .error { kind := .parseError, message := "truncated T entry in git diff -z" }
    | ['U'] =>
      match rest with
      | path :: tail => (parseDiffTokensSpec tail).map ({ kind := .unmerged, path := path } :: ·)
      | [] => .error { kind := .parseError, message := "truncated U entry in git diff -z" }
    | 'R' :: scoreChars =>
      match parseSimilarityScore scoreChars, rest with
      | some score, orig :: path :: tail =>
        (parseDiffTokensSpec tail).map
          ({ kind := .renamed score, path := path, origPath := some orig } :: ·)
      | none, _ =>
        .error { kind := .parseError, message := s!"invalid rename score in '{tok}'" }
      | _, _ =>
        .error { kind := .parseError, message := s!"truncated rename entry '{tok}' in git diff -z" }
    | 'C' :: scoreChars =>
      match parseSimilarityScore scoreChars, rest with
      | some score, orig :: path :: tail =>
        (parseDiffTokensSpec tail).map
          ({ kind := .copied score, path := path, origPath := some orig } :: ·)
      | none, _ =>
        .error { kind := .parseError, message := s!"invalid copy score in '{tok}'" }
      | _, _ =>
        .error { kind := .parseError, message := s!"truncated copy entry '{tok}' in git diff -z" }
    | _ =>
      .error { kind := .parseError, message := s!"unknown git diff status token: '{tok}'" }

private theorem splitNulRecordsLoop_eq (acc : List Char) (revOut : List String) (cs : List Char) :
    splitNulRecordsLoop acc revOut cs = (splitNulRecordsSpec acc cs).map (revOut.reverse ++ ·) := by
  induction cs generalizing acc revOut with
  | nil =>
    simp only [splitNulRecordsLoop, splitNulRecordsSpec]
    split <;> simp [Option.map]
  | cons c cs ih =>
    simp only [splitNulRecordsLoop, splitNulRecordsSpec]
    split
    · split
      · simp
      · rw [ih [] (String.ofList acc.reverse :: revOut)]
        cases splitNulRecordsSpec [] cs <;> simp [Option.map, List.reverse_cons, List.append_assoc]
    · exact ih (c :: acc) revOut

private theorem splitNulTokensAllowEmptyLoop_eq (acc : List Char) (revOut : List String)
    (cs : List Char) :
    splitNulTokensAllowEmptyLoop acc revOut cs =
      (splitNulTokensAllowEmptySpec acc cs).map (revOut.reverse ++ ·) := by
  induction cs generalizing acc revOut with
  | nil =>
    simp only [splitNulTokensAllowEmptyLoop, splitNulTokensAllowEmptySpec]
    split <;> simp [Option.map]
  | cons c cs ih =>
    simp only [splitNulTokensAllowEmptyLoop, splitNulTokensAllowEmptySpec]
    split
    · rw [ih [] (String.ofList acc.reverse :: revOut)]
      cases splitNulTokensAllowEmptySpec [] cs <;> simp [Option.map, List.reverse_cons, List.append_assoc]
    · exact ih (c :: acc) revOut

private theorem splitWorktreeStanzasLoop_tok (cur : List String) (revOut : List (List String))
    (tok : String) (rest : List String) (hne : tok ≠ "") :
    splitWorktreeStanzasLoop cur revOut (tok :: rest) =
      splitWorktreeStanzasLoop (tok :: cur) revOut rest := by
  conv => lhs; unfold splitWorktreeStanzasLoop
  split <;> rename_i heq <;> cases heq
  · exact absurd rfl hne
  · rfl

private theorem splitWorktreeStanzas_tok_local (cur : List String) (tok : String) (rest : List String)
    (hne : tok ≠ "") :
    splitWorktreeStanzasSpec cur (tok :: rest) = splitWorktreeStanzasSpec (tok :: cur) rest := by
  conv => lhs; unfold splitWorktreeStanzasSpec
  split <;> rename_i heq <;> cases heq
  · exact absurd rfl hne
  · rfl

private theorem splitWorktreeStanzasLoop_eq (cur : List String) (revOut : List (List String))
    (xs : List String) :
    splitWorktreeStanzasLoop cur revOut xs =
      (splitWorktreeStanzasSpec cur xs).map (revOut.reverse ++ ·) := by
  induction xs generalizing cur revOut with
  | nil =>
    unfold splitWorktreeStanzasLoop splitWorktreeStanzasSpec
    split <;> simp [Option.map]
  | cons tok rest ih =>
    by_cases htok : tok = ""
    · subst htok
      simp only [splitWorktreeStanzasLoop, splitWorktreeStanzasSpec]
      split
      · simp
      · rw [ih [] (cur.reverse :: revOut)]
        cases splitWorktreeStanzasSpec [] rest <;> simp [Option.map, List.reverse_cons, List.append_assoc]
    · rw [splitWorktreeStanzasLoop_tok cur revOut tok rest htok,
        splitWorktreeStanzas_tok_local cur tok rest htok]
      exact ih (tok :: cur) revOut

private theorem parseWorktreeStanzasLoop_eq (revOut : List WorktreeInfo) (xs : List (List String)) :
    parseWorktreeStanzasLoop revOut xs =
      (parseWorktreeStanzasSpec xs).map (revOut.reverse ++ ·) := by
  induction xs generalizing revOut with
  | nil => simp [parseWorktreeStanzasLoop, parseWorktreeStanzasSpec, Except.map]
  | cons st rest ih =>
    unfold parseWorktreeStanzasLoop parseWorktreeStanzasSpec
    dsimp only [bind, Except.bind, pure, Except.pure]
    cases parseWorktreeStanza st with
    | error e => simp [Except.map]
    | ok info =>
      dsimp only
      rw [ih (info :: revOut)]
      cases parseWorktreeStanzasSpec rest <;> simp [Except.map, List.reverse_cons, List.append_assoc]

private theorem parsePorcelainStatusLoop_eq (revOut : List StatusEntry) (xs : List String) :
    parsePorcelainStatusLoop revOut xs =
      (parsePorcelainStatusSpec xs).map (revOut.reverse ++ ·) := by
  match xs with
  | [] => simp [parsePorcelainStatusLoop, parsePorcelainStatusSpec, Except.map]
  | recStr :: rest =>
    unfold parsePorcelainStatusLoop parsePorcelainStatusSpec
    split
    · next x y pathChars heq =>
      simp only [heq]
      split
      · simp [Except.map, *]
      · split
        · split
          · cases rest with
            | nil => simp [Except.map, *]
            | cons orig tail =>
              dsimp only
              rw [parsePorcelainStatusLoop_eq _ tail]
              cases parsePorcelainStatusSpec tail <;>
                simp [Except.map, List.reverse_cons, List.append_assoc, *]
          · rw [parsePorcelainStatusLoop_eq _ rest]
            cases parsePorcelainStatusSpec rest <;>
              simp [Except.map, List.reverse_cons, List.append_assoc, *]
        · simp [Except.map, *]
    · simp [Except.map, *]
termination_by xs.length

private theorem parseDiffTokensLoop_eq (revOut : List DiffEntry) (xs : List String) :
    parseDiffTokensLoop revOut xs =
      (parseDiffTokensSpec xs).map (revOut.reverse ++ ·) := by
  match xs with
  | [] => simp [parseDiffTokensLoop, parseDiffTokensSpec, Except.map]
  | tok :: rest =>
    unfold parseDiffTokensLoop parseDiffTokensSpec
    split
    · next heq =>
      simp only [heq]
      cases rest with
      | nil => simp [Except.map]
      | cons _ tail =>
        dsimp only
        rw [parseDiffTokensLoop_eq _ tail]
        cases parseDiffTokensSpec tail <;> simp [Except.map, List.reverse_cons, List.append_assoc]
    · next heq =>
      simp only [heq]
      cases rest with
      | nil => simp [Except.map]
      | cons _ tail =>
        dsimp only
        rw [parseDiffTokensLoop_eq _ tail]
        cases parseDiffTokensSpec tail <;> simp [Except.map, List.reverse_cons, List.append_assoc]
    · next heq =>
      simp only [heq]
      cases rest with
      | nil => simp [Except.map]
      | cons _ tail =>
        dsimp only
        rw [parseDiffTokensLoop_eq _ tail]
        cases parseDiffTokensSpec tail <;> simp [Except.map, List.reverse_cons, List.append_assoc]
    · next heq =>
      simp only [heq]
      cases rest with
      | nil => simp [Except.map]
      | cons _ tail =>
        dsimp only
        rw [parseDiffTokensLoop_eq _ tail]
        cases parseDiffTokensSpec tail <;> simp [Except.map, List.reverse_cons, List.append_assoc]
    · next heq =>
      simp only [heq]
      cases rest with
      | nil => simp [Except.map]
      | cons _ tail =>
        dsimp only
        rw [parseDiffTokensLoop_eq _ tail]
        cases parseDiffTokensSpec tail <;> simp [Except.map, List.reverse_cons, List.append_assoc]
    · next scoreChars heq =>
      simp only [heq]
      split
      · rw [parseDiffTokensLoop_eq]
        cases h : parseDiffTokensSpec _ <;>
          simp [Except.map, List.reverse_cons, List.append_assoc, *]
      · simp [Except.map, *]
      · simp [Except.map, *]
    · next scoreChars heq =>
      simp only [heq]
      split
      · rw [parseDiffTokensLoop_eq]
        cases h : parseDiffTokensSpec _ <;>
          simp [Except.map, List.reverse_cons, List.append_assoc, *]
      · simp [Except.map, *]
      · simp [Except.map, *]
    · simp [Except.map, *]
termination_by xs.length

private theorem splitNulRecordsAux_eof (acc cs : List Char)
    (hno : hasNulChar cs = false) (hne : ¬ (acc = [] ∧ cs = [])) :
    splitNulRecordsSpec acc cs = none := by
  induction cs generalizing acc with
  | nil =>
    have hacc : acc ≠ [] := fun h => hne ⟨h, rfl⟩
    simp [splitNulRecordsSpec, hacc]
  | cons c cs ih =>
    have hc : c ≠ Char.ofNat 0 := hasNulChar_eq_false_iff.mp hno c List.mem_cons_self
    have hcs : hasNulChar cs = false :=
      hasNulChar_eq_false_iff.mpr fun x hx =>
        hasNulChar_eq_false_iff.mp hno x (List.mem_cons_of_mem c hx)
    have hne' : ¬ (c :: acc = [] ∧ cs = []) := fun ⟨h, _⟩ => by cases h
    have hbeq : (c == Char.ofNat 0) = false := beq_false_of_ne hc
    simp [splitNulRecordsSpec, hbeq, ih (c :: acc) hcs hne']

private theorem toUTF8_nonempty_of_ne {s : String} (hne : s ≠ "") : s.toUTF8.isEmpty = false :=
  Bool.eq_false_iff.mpr fun hc => hne ((toUTF8_eq_empty_iff s).mp hc)

private theorem splitNulRecordsAux_append_nul (acc cs rest : List Char)
    (hno : hasNulChar cs = false) (hne : ¬ (acc = [] ∧ cs = [])) :
    splitNulRecordsSpec acc (cs ++ Char.ofNat 0 :: rest) =
      (splitNulRecordsSpec [] rest).map (String.ofList (acc.reverse ++ cs) :: ·) := by
  induction cs generalizing acc with
  | nil =>
    have hacc : acc ≠ [] := fun h => hne ⟨h, rfl⟩
    have hem : acc.isEmpty = false := by
      cases acc with
      | nil => contradiction
      | cons _ _ => rfl
    simp [splitNulRecordsSpec, hem]
  | cons c cs ih =>
    have hc : c ≠ Char.ofNat 0 := hasNulChar_eq_false_iff.mp hno c List.mem_cons_self
    have hcs : hasNulChar cs = false :=
      hasNulChar_eq_false_iff.mpr fun x hx =>
        hasNulChar_eq_false_iff.mp hno x (List.mem_cons_of_mem c hx)
    have hne' : ¬ (c :: acc = [] ∧ cs = []) := fun ⟨h, _⟩ => by cases h
    have hbeq : (c == Char.ofNat 0) = false := beq_false_of_ne hc
    simp [splitNulRecordsSpec, hbeq, ih (c :: acc) hcs hne', List.reverse_cons, List.append_assoc]

/-- Proof of `test_git_cleanGitEnv_stripsInheritedGitKeys` for `cleanGitEnv`. -/
theorem proof_git_cleanGitEnv_stripsInheritedGitKeys :
    AllPass (test_git_cleanGitEnv_stripsInheritedGitKeys (fun inh ext => cleanGitEnv inh ext)) := by
  intro inherited extra
  simp only [cleanGitEnv, assert]
  refine ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩
  · simp only [List.all_eq_true]
    intro kv hkv
    by_cases hgit : (isGitKey kv.1 || isLocaleKey kv.1) = true
    · simp only [Bool.or_eq_true, List.contains_iff_mem, List.mem_append,
        List.mem_map, List.mem_filter]
      exact Or.inr (Or.inl (Or.inl ⟨kv, ⟨hkv, (Bool.or_eq_true _ _).mp hgit⟩, rfl⟩))
    · simp only [Bool.or_eq_true] at hgit
      have hng : isGitKey kv.1 = false := Bool.eq_false_iff.mpr (fun h => hgit (Or.inl h))
      have hnl : isLocaleKey kv.1 = false := Bool.eq_false_iff.mpr (fun h => hgit (Or.inr h))
      simp [hng, hnl]
  · simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append]
    intro kv hkv
    exact Or.inl (Or.inr hkv)
  · simp only [List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      beq_iff_eq, List.contains_iff_mem]
    intro kv hkv
    simp only [List.mem_append, List.mem_map, List.mem_filter] at hkv
    rcases hkv with (⟨p, _, rfl⟩ | hdef) | ⟨_, hvalid⟩
    · exact Or.inl (Or.inl (Or.inr rfl))
    · exact Or.inl (Or.inr hdef)
    · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hvalid
      rcases hvalid with ⟨⟨⟨_, _⟩, hng | hallow⟩, hnl⟩
      · exact Or.inl (Or.inl (Or.inl ⟨hng, hnl⟩))
      · exact Or.inr hallow

/-- Proof of `test_git_cleanGitEnv_preservesValidNonGitExtra` for `cleanGitEnv`. -/
theorem proof_git_cleanGitEnv_preservesValidNonGitExtra :
    AllPass (test_git_cleanGitEnv_preservesValidNonGitExtra (fun inh ext => cleanGitEnv inh ext)) := by
  intro _inherited key val hKey hVal hNotGit hNotLocale
  simp only [cleanGitEnv, assert, List.contains_iff_mem,
    List.mem_append, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨Or.inr ⟨trivial, by simp [hKey, hVal, hNotGit, hNotLocale]⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_cleanGitEnv_preservesValidNonGitExtra`. -/
theorem reach_git_cleanGitEnv_preservesValidNonGitExtra :
    CanReach (test_git_cleanGitEnv_preservesValidNonGitExtra (fun inh ext => cleanGitEnv inh ext)) :=
  ⟨#[], "FOO", some "bar", rfl, rfl, rfl, rfl,
    proof_git_cleanGitEnv_preservesValidNonGitExtra #[] "FOO" (some "bar") rfl rfl rfl rfl⟩

/-- Proof of `test_git_mkCommitId_validatesHexLengthAndChars` for `mkCommitId`. -/
theorem proof_git_mkCommitId_validatesHexLengthAndChars :
    AllPass (test_git_mkCommitId_validatesHexLengthAndChars mkCommitId) := by
  intro s
  dsimp [test_git_mkCommitId_validatesHexLengthAndChars, AllPass, bind, assert, mkCommitId]
  split
  · next h => exact ⟨⟨rfl, h⟩, trivial⟩
  · next h =>
    have hf : isValidCommitIdStr s = false := Bool.eq_false_iff.mpr h
    exact ⟨⟨rfl, by simp [toString], hf⟩, trivial⟩

/-- Proof of `test_git_mkRefName_rejectsUnsafeRefs` for `mkRefName`. -/
theorem proof_git_mkRefName_rejectsUnsafeRefs :
    AllPass (test_git_mkRefName_rejectsUnsafeRefs mkRefName) := by
  intro s hbad
  have hFalse : isValidRefNameStr s = false := by
    unfold isValidRefNameStr
    rcases hbad with rfl | rfl | hhead | rfl | hdots
    · rfl
    · rfl
    · simp [hhead]
    · rfl
    · simp [hdots]
  simp only [mkRefName, hFalse, Bool.false_eq_true, ↓reduceIte, assert, toString]
  simp

/-- Non-vacuity `CanReach` witness for `test_git_mkRefName_rejectsUnsafeRefs`. -/
theorem reach_git_mkRefName_rejectsUnsafeRefs :
    CanReach (test_git_mkRefName_rejectsUnsafeRefs mkRefName) := by
  exact ⟨"-rf", Or.inr (Or.inr (Or.inl rfl)), ⟨rfl, by decide⟩, trivial⟩

/-- Proof of `test_git_parsePorcelainStatusZ_framingAndEmpty` for `parsePorcelainStatusZ`. -/
theorem proof_git_parsePorcelainStatusZ_framingAndEmpty :
    AllPass (test_git_parsePorcelainStatusZ_framingAndEmpty parsePorcelainStatusZ) := by
  dsimp only [test_git_parsePorcelainStatusZ_framingAndEmpty, AllPass, assert]
  have hEmpty : parsePorcelainStatusZ ByteArray.empty = .ok #[] := rfl
  have hBad : parsePorcelainStatusZ (" M a.txt" : String).toUTF8 =
      .error { kind := .parseError, message := "unterminated or empty record in git status -z output" } := by
    unfold parsePorcelainStatusZ
    rw [toUTF8_nonempty_of_ne (by decide), fromUTF8_toUTF8]
    dsimp only
    have hSplit : splitNulRecords " M a.txt" = none := by
      unfold splitNulRecords
      rw [splitNulRecordsLoop_eq,
        splitNulRecordsAux_eof [] " M a.txt".toList (by decide) (by intro ⟨_, hc⟩; cases hc)]
      rfl
    rw [hSplit]
    rfl
  exact ⟨hEmpty, ⟨{ kind := .parseError, message := "unterminated or empty record in git status -z output" },
    hBad, rfl, fun h => by have hl := congrArg String.length h; contradiction⟩, trivial⟩

private theorem prefix_rename_status_no_nul (dst : String) (hdst : hasNulChar dst.toList = false) :
    hasNulChar ('R' :: ' ' :: ' ' :: dst.toList) = false := by
  simp [hasNulChar, hdst]

private theorem parsePorcelainStatusZ_renameDestFirst_eq (src dst : String)
    (hsrc : src ≠ "" ∧ (!hasNulChar src.toList) = true)
    (hdst : dst ≠ "" ∧ (!hasNulChar dst.toList) = true) :
    parsePorcelainStatusZ ("R  " ++ dst ++ "\x00" ++ src ++ "\x00").toUTF8 =
      .ok #[{ indexStatus := some .renamed, worktreeStatus := none, path := dst, origPath := some src }] := by
  rcases hsrc with ⟨hsrcNe, hsrcNul⟩
  rcases hdst with ⟨hdstNe, hdstNul⟩
  have hsrcNul' : hasNulChar src.toList = false := by simpa using hsrcNul
  have hdstNul' : hasNulChar dst.toList = false := by simpa using hdstNul
  let s := "R  " ++ dst ++ "\x00" ++ src ++ "\x00"
  have hsNe : s ≠ "" := by
    intro h
    simp [s, String.append_eq_empty_iff] at h
  have hEmptyFalse : s.toUTF8.isEmpty = false :=
    Bool.eq_false_iff.mpr fun hc => hsNe ((toUTF8_eq_empty_iff s).mp hc)
  have hsList : s.toList = ('R' :: ' ' :: ' ' :: dst.toList) ++ Char.ofNat 0 :: (src.toList ++ [Char.ofNat 0]) := by
    simp [s, String.toList_append, List.append_assoc]
  have hSplit1 := splitNulRecordsAux_append_nul [] ('R' :: ' ' :: ' ' :: dst.toList)
    (src.toList ++ [Char.ofNat 0]) (prefix_rename_status_no_nul dst hdstNul') (by intro ⟨_, hc⟩; cases hc)
  have hSplit2 := splitNulRecordsAux_append_nul [] src.toList [] hsrcNul'
    (by intro ⟨_, hc⟩; apply hsrcNe; exact String.toList_injective hc)
  have hRPrefix : String.ofList ('R' :: ' ' :: ' ' :: dst.toList) = "R  " ++ dst := by
    have h1 : ('R' :: ' ' :: ' ' :: dst.toList) = ['R', ' ', ' '] ++ dst.toList := rfl
    rw [h1, string_ofList_append]
    simp [String.ofList_toList]
  have hSplit : splitNulRecords s = some ["R  " ++ dst, src] := by
    unfold splitNulRecords
    rw [splitNulRecordsLoop_eq, hsList, hSplit1, hSplit2]
    simp [splitNulRecordsSpec, hRPrefix, String.ofList_toList]
  have hDstChars : dst.toList ≠ [] := fun hc => hdstNe (String.toList_injective hc)
  have hDstEmpty : dst.toList.isEmpty = false := by
    cases h : dst.toList with
    | nil => exact absurd h hDstChars
    | cons _ _ => rfl
  have hRecList : ("R  " ++ dst).toList = 'R' :: ' ' :: ' ' :: dst.toList := by
    simp [String.toList_append]
  unfold parsePorcelainStatusZ
  rw [hEmptyFalse, fromUTF8_toUTF8]
  dsimp only
  rw [hSplit]
  simp only [bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte,
    parsePorcelainStatusLoop_eq]
  have hRecs : parsePorcelainStatusSpec ["R  " ++ dst, src] =
      .ok [{ indexStatus := some .renamed, worktreeStatus := none, path := dst, origPath := some src }] := by
    unfold parsePorcelainStatusSpec
    rw [hRecList]
    split
    · next x y pathChars heq =>
      cases heq
      have hPair : isValidStatusPair 'R' ' ' = true := by decide
      have hEnd : parsePorcelainStatusSpec [] = .ok [] := rfl
      simp [hDstEmpty, hPair, statusCharToKind?, hEnd, Except.map, String.ofList_toList]
    · next h => exact absurd rfl (h 'R' ' ' dst.toList)
  rw [hRecs]
  rfl

/-- Proof of `test_git_parsePorcelainStatusZ_renameDestFirst` for `parsePorcelainStatusZ`. -/
theorem proof_git_parsePorcelainStatusZ_renameDestFirst :
    AllPass (test_git_parsePorcelainStatusZ_renameDestFirst parsePorcelainStatusZ) := by
  intro src dst hsrc hdst
  dsimp only [assert]
  rw [parsePorcelainStatusZ_renameDestFirst_eq src dst hsrc hdst]
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_parsePorcelainStatusZ_renameDestFirst`. -/
theorem reach_git_parsePorcelainStatusZ_renameDestFirst :
    CanReach (test_git_parsePorcelainStatusZ_renameDestFirst parsePorcelainStatusZ) := by
  refine ⟨"src.txt", "dest.txt", ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩
  dsimp only [assert]
  rw [parsePorcelainStatusZ_renameDestFirst_eq "src.txt" "dest.txt" ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
  exact ⟨rfl, trivial⟩

private theorem parseDiffNameStatusZ_renameSourceFirst_eq (src dst : String)
    (hsrc : src ≠ "" ∧ (!hasNulChar src.toList) = true)
    (hdst : dst ≠ "" ∧ (!hasNulChar dst.toList) = true) :
    parseDiffNameStatusZ ("R095\x00" ++ src ++ "\x00" ++ dst ++ "\x00").toUTF8 =
      .ok #[{ kind := .renamed 95, path := dst, origPath := some src }] := by
  rcases hsrc with ⟨hsrcNe, hsrcNul⟩
  rcases hdst with ⟨hdstNe, hdstNul⟩
  have hsrcNul' : hasNulChar src.toList = false := by simpa using hsrcNul
  have hdstNul' : hasNulChar dst.toList = false := by simpa using hdstNul
  let s := "R095\x00" ++ src ++ "\x00" ++ dst ++ "\x00"
  have hsNe : s ≠ "" := by
    intro h
    simp [s, String.append_eq_empty_iff] at h
  have hEmptyFalse : s.toUTF8.isEmpty = false :=
    Bool.eq_false_iff.mpr fun hc => hsNe ((toUTF8_eq_empty_iff s).mp hc)
  have hsList : s.toList = ['R', '0', '9', '5'] ++ Char.ofNat 0 :: (src.toList ++ Char.ofNat 0 :: (dst.toList ++ [Char.ofNat 0])) := by
    simp [s, String.toList_append, List.append_assoc]
  have hSplit1 := splitNulRecordsAux_append_nul [] ['R', '0', '9', '5']
    (src.toList ++ Char.ofNat 0 :: (dst.toList ++ [Char.ofNat 0])) (by decide) (by intro ⟨_, hc⟩; cases hc)
  have hSplit2 := splitNulRecordsAux_append_nul [] src.toList
    (dst.toList ++ [Char.ofNat 0]) hsrcNul' (by intro ⟨_, hc⟩; apply hsrcNe; exact String.toList_injective hc)
  have hSplit3 := splitNulRecordsAux_append_nul [] dst.toList [] hdstNul'
    (by intro ⟨_, hc⟩; apply hdstNe; exact String.toList_injective hc)
  have hSplit : splitNulRecords s = some ["R095", src, dst] := by
    unfold splitNulRecords
    rw [splitNulRecordsLoop_eq, hsList, hSplit1, hSplit2, hSplit3]
    simp [splitNulRecordsSpec, String.ofList_toList]
  unfold parseDiffNameStatusZ
  rw [hEmptyFalse, fromUTF8_toUTF8]
  dsimp only
  rw [hSplit]
  simp only [bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte,
    parseDiffTokensLoop_eq]
  have hDiffs : parseDiffTokensSpec ["R095", src, dst] =
      .ok [{ kind := .renamed 95, path := dst, origPath := some src }] := by
    unfold parseDiffTokensSpec
    rw [show ("R095" : String).toList = ['R', '0', '9', '5'] from by decide]
    split
    all_goals
      first
      | (next _ heq => cases heq)
      | (next scoreChars heq =>
          cases heq
          have hScore : parseSimilarityScore ['0', '9', '5'] = some 95 := by decide
          have hEnd : parseDiffTokensSpec [] = .ok [] := rfl
          simp [hScore, hEnd, Except.map])
      | (next _ _ _ _ _ hR _ => exact absurd rfl (hR ['0', '9', '5']))
  rw [hDiffs]
  rfl

/-- Proof of `test_git_parseDiffNameStatusZ_renameSourceFirst` for `parseDiffNameStatusZ`. -/
theorem proof_git_parseDiffNameStatusZ_renameSourceFirst :
    AllPass (test_git_parseDiffNameStatusZ_renameSourceFirst parseDiffNameStatusZ) := by
  intro src dst hsrc hdst
  dsimp only [assert]
  rw [parseDiffNameStatusZ_renameSourceFirst_eq src dst hsrc hdst]
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_git_parseDiffNameStatusZ_renameSourceFirst`. -/
theorem reach_git_parseDiffNameStatusZ_renameSourceFirst :
    CanReach (test_git_parseDiffNameStatusZ_renameSourceFirst parseDiffNameStatusZ) := by
  refine ⟨"src.txt", "dest.txt", ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_⟩
  dsimp only [assert]
  rw [parseDiffNameStatusZ_renameSourceFirst_eq "src.txt" "dest.txt" ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
  exact ⟨rfl, trivial⟩

private theorem splitNulTokensAllowEmptyAux_append_nul (acc cs rest : List Char)
    (hno : hasNulChar cs = false) :
    splitNulTokensAllowEmptySpec acc (cs ++ Char.ofNat 0 :: rest) =
      (splitNulTokensAllowEmptySpec [] rest).map (String.ofList (acc.reverse ++ cs) :: ·) := by
  induction cs generalizing acc with
  | nil => simp [splitNulTokensAllowEmptySpec]
  | cons c cs ih =>
    have hc : c ≠ Char.ofNat 0 := hasNulChar_eq_false_iff.mp hno c List.mem_cons_self
    have hcs : hasNulChar cs = false :=
      hasNulChar_eq_false_iff.mpr fun x hx => hasNulChar_eq_false_iff.mp hno x (List.mem_cons_of_mem c hx)
    have hbeq : (c == Char.ofNat 0) = false := beq_false_of_ne hc
    simp [splitNulTokensAllowEmptySpec, hbeq, ih (c :: acc) hcs, List.reverse_cons, List.append_assoc]

private theorem splitWorktreeStanzas_empty (cur rest : List String) (hne : cur.isEmpty = false) :
    splitWorktreeStanzasSpec cur ("" :: rest) = (splitWorktreeStanzasSpec [] rest).map (cur.reverse :: ·) := by
  conv => lhs; unfold splitWorktreeStanzasSpec
  simp [hne]

private theorem splitWorktreeStanzas_tok (cur : List String) (tok : String) (rest : List String)
    (hne : tok ≠ "") :
    splitWorktreeStanzasSpec cur (tok :: rest) = splitWorktreeStanzasSpec (tok :: cur) rest := by
  conv => lhs; unfold splitWorktreeStanzasSpec
  split <;> rename_i heq <;> cases heq
  · exact absurd rfl hne
  · rfl

private theorem parseWorktreeAttrs_bare (info : WorktreeInfo) (hs : Bool) (rest : List String) :
    parseWorktreeAttrs info hs ("bare" :: rest) =
      parseWorktreeAttrs { info with isBare := true } hs rest := rfl

private theorem parseWorktreeAttrs_detached (info : WorktreeInfo) (hs : Bool) (rest : List String) :
    parseWorktreeAttrs info hs ("detached" :: rest) =
      parseWorktreeAttrs { info with isDetached := true } hs rest := rfl

private theorem parseWorktreeAttrs_locked (info : WorktreeInfo) (hs : Bool) (rest : List String) :
    parseWorktreeAttrs info hs ("locked" :: rest) =
      parseWorktreeAttrs { info with isLocked := true, lockReason := none } hs rest := rfl

private theorem list_all_replicate_true {α : Type} (n : Nat) (x : α) (p : α → Bool)
    (hp : p x = true) : (List.replicate n x).all p = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, hp, ih]

private theorem hasNulChar_head_rep40 (n : Nat) (ch : Char) (hch : ch ≠ Char.ofNat 0) :
    hasNulChar ("HEAD " ++ String.ofList (List.replicate n ch)).toList = false := by
  rw [hasNulChar_eq_false_iff, String.toList_append, String.toList_ofList]
  intro c hc
  rw [List.mem_append] at hc
  rcases hc with hc | hc
  · have hno : hasNulChar "HEAD ".toList = false := by decide
    exact hasNulChar_eq_false_iff.mp hno c hc
  · rw [String.toList_ofList] at hc
    rcases List.mem_replicate.mp hc with ⟨_, rfl⟩
    exact hch

private theorem isAllZeros_rep40_zero :
    isAllZerosCommitStr (String.ofList (List.replicate 40 '0')) = true := by
  unfold isAllZerosCommitStr
  rw [String.toList_ofList]
  dsimp only
  rw [List.length_replicate, list_all_replicate_true _ _ _ (by decide)]
  rfl

private theorem isAllZeros_rep40_a :
    isAllZerosCommitStr (String.ofList (List.replicate 40 'a')) = false := by
  unfold isAllZerosCommitStr
  rw [String.toList_ofList]
  simp [List.replicate_succ]

private theorem isValidCommitIdStr_rep40_a :
    isValidCommitIdStr (String.ofList (List.replicate 40 'a')) = true := by
  unfold isValidCommitIdStr
  rw [String.toList_ofList]
  dsimp only
  rw [List.length_replicate, list_all_replicate_true _ _ _ (by decide)]
  rfl

private theorem stripPrefixChars_append (p cs : List Char) :
    stripPrefixChars p (p ++ cs) = some cs := by
  induction p with
  | nil => rfl
  | cons x xs ih => simp [stripPrefixChars, ih]

private theorem head_str_ne_empty (sha : String) : ("HEAD " ++ sha) ≠ "" := by
  intro heq
  have ht := congrArg (fun s : String => s.toList.head?) heq
  rw [String.toList_append, show ("HEAD " : String).toList = ['H', 'E', 'A', 'D', ' '] from rfl] at ht
  cases ht

private theorem head_str_ne_tag (sha tag : String) (h : tag.toList.head? ≠ some 'H') :
    ("HEAD " ++ sha == tag) = false := by
  apply beq_false_of_ne
  intro heq
  have ht := congrArg (fun s : String => s.toList.head?) heq
  rw [String.toList_append, show ("HEAD " : String).toList = ['H', 'E', 'A', 'D', ' '] from rfl] at ht
  exact h ht.symm

private theorem parseWorktreeAttrs_head_zeros (info : WorktreeInfo) (hs : Bool)
    (sha : String) (rest : List String) (hz : isAllZerosCommitStr sha = true) :
    parseWorktreeAttrs info hs (("HEAD " ++ sha) :: rest) =
      parseWorktreeAttrs { info with head? := none } true rest := by
  have hB := head_str_ne_tag sha "bare" (by decide)
  have hD := head_str_ne_tag sha "detached" (by decide)
  have hL := head_str_ne_tag sha "locked" (by decide)
  have hP := head_str_ne_tag sha "prunable" (by decide)
  have hPref : stripPrefixChars ['H', 'E', 'A', 'D', ' '] ("HEAD " ++ sha).toList = some sha.toList := by
    rw [String.toList_append, show ("HEAD " : String).toList = ['H', 'E', 'A', 'D', ' '] from rfl]
    exact stripPrefixChars_append ['H', 'E', 'A', 'D', ' '] sha.toList
  conv => lhs; unfold parseWorktreeAttrs
  simp only [hB, hD, hL, hP, Bool.false_eq_true, ↓reduceIte, hPref, String.ofList_toList, hz]

private theorem parseWorktreeAttrs_head_commit (info : WorktreeInfo) (hs : Bool)
    (sha : String) (cid : CommitId) (rest : List String)
    (hz : isAllZerosCommitStr sha = false) (hCid : mkCommitId sha = .ok cid) :
    parseWorktreeAttrs info hs (("HEAD " ++ sha) :: rest) =
      parseWorktreeAttrs { info with head? := some cid } true rest := by
  have hB := head_str_ne_tag sha "bare" (by decide)
  have hD := head_str_ne_tag sha "detached" (by decide)
  have hL := head_str_ne_tag sha "locked" (by decide)
  have hP := head_str_ne_tag sha "prunable" (by decide)
  have hPref : stripPrefixChars ['H', 'E', 'A', 'D', ' '] ("HEAD " ++ sha).toList = some sha.toList := by
    rw [String.toList_append, show ("HEAD " : String).toList = ['H', 'E', 'A', 'D', ' '] from rfl]
    exact stripPrefixChars_append ['H', 'E', 'A', 'D', ' '] sha.toList
  conv => lhs; unfold parseWorktreeAttrs
  simp only [hB, hD, hL, hP, Bool.false_eq_true, ↓reduceIte, hPref, String.ofList_toList, hz, hCid]

private theorem parseWorktreeAttrs_branch (info : WorktreeInfo) (hs : Bool)
    (line refStr shortStr : String) (ref : RefName) (rest : List String)
    (hB : (line == "bare") = false) (hD : (line == "detached") = false)
    (hL : (line == "locked") = false) (hP : (line == "prunable") = false)
    (hNoH : stripPrefixChars ['H', 'E', 'A', 'D', ' '] line.toList = none)
    (hBr : stripPrefixChars ['b', 'r', 'a', 'n', 'c', 'h', ' '] line.toList = some refStr.toList)
    (hRh : stripPrefixChars ['r', 'e', 'f', 's', '/', 'h', 'e', 'a', 'd', 's', '/'] refStr.toList =
      some shortStr.toList)
    (hRef : mkRefName shortStr = .ok ref) :
    parseWorktreeAttrs info hs (line :: rest) =
      parseWorktreeAttrs { info with branch? := some ref } hs rest := by
  conv => lhs; unfold parseWorktreeAttrs
  simp only [hB, hD, hL, hP, Bool.false_eq_true, ↓reduceIte, hNoH, hBr, hRh, String.ofList_toList, hRef]

private theorem parseWorktreeAttrs_prunable_reason (info : WorktreeInfo) (hs : Bool)
    (line reason : String) (rest : List String)
    (hB : (line == "bare") = false) (hD : (line == "detached") = false)
    (hL : (line == "locked") = false) (hP : (line == "prunable") = false)
    (hNoH : stripPrefixChars ['H', 'E', 'A', 'D', ' '] line.toList = none)
    (hNoBr : stripPrefixChars ['b', 'r', 'a', 'n', 'c', 'h', ' '] line.toList = none)
    (hNoLk : stripPrefixChars ['l', 'o', 'c', 'k', 'e', 'd', ' '] line.toList = none)
    (hPr : stripPrefixChars ['p', 'r', 'u', 'n', 'a', 'b', 'l', 'e', ' '] line.toList = some reason.toList) :
    parseWorktreeAttrs info hs (line :: rest) =
      parseWorktreeAttrs { info with isPrunable := true, pruneReason := some reason } hs rest := by
  conv => lhs; unfold parseWorktreeAttrs
  simp only [hB, hD, hL, hP, Bool.false_eq_true, ↓reduceIte, hNoH, hNoBr, hNoLk, hPr, String.ofList_toList]

private theorem parseWorktreeStanza_worktree (header path : String) (attrs : List String)
    (hHdr : stripPrefixChars ['w', 'o', 'r', 'k', 't', 'r', 'e', 'e', ' '] header.toList = some path.toList)
    (hNe : path.toList.isEmpty = false) :
    parseWorktreeStanza (header :: attrs) =
      Except.bind (parseWorktreeAttrs { path := path, head? := none, branch? := none } false attrs)
        (fun p =>
          if !p.1.isBare && !p.2 then
            .error { kind := .parseError, message := s!"non-bare worktree '{p.1.path}' missing HEAD attribute" }
          else
            .ok p.1) := by
  unfold parseWorktreeStanza
  simp only [hHdr, hNe, Bool.false_eq_true, ↓reduceIte, String.ofList_toList]
  rfl

private theorem parseWorktreeListPorcelain_ok_of (s : String) (toks : List String)
    (stanzas : List (List String)) (infos : List WorktreeInfo)
    (hNe : s.toUTF8.isEmpty = false)
    (hToks : splitNulTokensAllowEmptySpec [] s.toList = some toks)
    (hStz : splitWorktreeStanzasSpec [] toks = some stanzas)
    (hInfos : parseWorktreeStanzasSpec stanzas = .ok infos) :
    parseWorktreeListPorcelain s.toUTF8 = .ok infos.toArray := by
  unfold parseWorktreeListPorcelain
  rw [hNe, fromUTF8_toUTF8]
  dsimp only
  rw [splitNulTokensAllowEmptyLoop_eq, hToks]
  dsimp only [Option.map, List.reverse_nil, List.nil_append]
  rw [splitWorktreeStanzasLoop_eq, hStz]
  dsimp only [Option.map, List.reverse_nil, List.nil_append]
  rw [parseWorktreeStanzasLoop_eq, hInfos]
  rfl

private theorem splitNulTokensAllowEmptyAux_step (a : String) (rest : List Char)
    (toks : List String)
    (hno : hasNulChar a.toList = false)
    (hrest : splitNulTokensAllowEmptySpec [] rest = some toks) :
    splitNulTokensAllowEmptySpec [] (a.toList ++ Char.ofNat 0 :: rest) = some (a :: toks) := by
  rw [splitNulTokensAllowEmptyAux_append_nul [] a.toList rest hno, hrest]
  simp [String.ofList_toList]

private theorem splitNulRecordsAux_step (a : String) (rest : List Char) (recs : List String)
    (hne : a ≠ "") (hno : hasNulChar a.toList = false)
    (hrest : splitNulRecordsSpec [] rest = some recs) :
    splitNulRecordsSpec [] (a.toList ++ Char.ofNat 0 :: rest) = some (a :: recs) := by
  have hacs : ¬ (([] : List Char) = [] ∧ a.toList = []) := fun h => hne (String.toList_injective h.2)
  rw [splitNulRecordsAux_append_nul [] a.toList rest hno hacs, hrest]
  simp [String.ofList_toList]

private theorem parsePorcelainStatusZ_ok_of (s : String) (toks : List String)
    (recs : List StatusEntry)
    (hNe : s.toUTF8.isEmpty = false)
    (hToks : splitNulRecordsSpec [] s.toList = some toks)
    (hRecs : parsePorcelainStatusSpec toks = .ok recs) :
    parsePorcelainStatusZ s.toUTF8 = .ok recs.toArray := by
  unfold parsePorcelainStatusZ
  rw [hNe, fromUTF8_toUTF8]
  dsimp only
  have hSplit : splitNulRecords s = some toks := by
    unfold splitNulRecords
    rw [splitNulRecordsLoop_eq, hToks]
    rfl
  rw [hSplit]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [parsePorcelainStatusLoop_eq, hRecs]
  rfl

private theorem parsePorcelainStatusRecords_plain (tok path : String) (x y : Char)
    (rest : List String) (kx ky : Option StatusKind)
    (hTok : tok.toList = x :: y :: ' ' :: path.toList)
    (hNe : path.toList.isEmpty = false) (hPair : isValidStatusPair x y = true)
    (hx : statusCharToKind? x = some kx) (hy : statusCharToKind? y = some ky)
    (hxNot : x ≠ 'R' ∧ x ≠ 'C') (hyNot : y ≠ 'R' ∧ y ≠ 'C') :
    parsePorcelainStatusSpec (tok :: rest) =
      (parsePorcelainStatusSpec rest).map
        ({ indexStatus := kx, worktreeStatus := ky, path := path } :: ·) := by
  conv => lhs; unfold parsePorcelainStatusSpec
  rw [hTok]
  split
  · next x' y' pathChars heq =>
    cases heq
    simp [hNe, hPair, hx, hy, hxNot.1, hxNot.2, hyNot.1, hyNot.2, String.ofList_toList]
  · next h => exact absurd rfl (h x y path.toList)

private theorem parsePorcelainStatusRecords_rc (tok path orig : String) (x y : Char)
    (rest : List String) (kx ky : Option StatusKind)
    (hTok : tok.toList = x :: y :: ' ' :: path.toList)
    (hNe : path.toList.isEmpty = false) (hPair : isValidStatusPair x y = true)
    (hx : statusCharToKind? x = some kx) (hy : statusCharToKind? y = some ky)
    (hRc : (x == 'R' || x == 'C') = true) :
    parsePorcelainStatusSpec (tok :: orig :: rest) =
      (parsePorcelainStatusSpec rest).map
        ({ indexStatus := kx, worktreeStatus := ky, path := path, origPath := some orig } :: ·) := by
  conv => lhs; unfold parsePorcelainStatusSpec
  rw [hTok]
  split
  · next x' y' pathChars heq =>
    cases heq
    simp [hNe, hPair, hx, hy, hRc, String.ofList_toList]
  · next h => exact absurd rfl (h x y path.toList)

/-- Proof of `test_git_parseWorktreeListPorcelain_bareUnbornLocked` for `parseWorktreeListPorcelain`. -/
theorem proof_git_parseWorktreeListPorcelain_bareUnbornLocked :
    AllPass (test_git_parseWorktreeListPorcelain_bareUnbornLocked parseWorktreeListPorcelain) := by
  have hBare : parseWorktreeListPorcelain "worktree /tmp/bare.git\x00bare\x00\x00".toUTF8 =
      .ok #[{ path := "/tmp/bare.git", head? := none, branch? := none, isBare := true }] := by
    let sb := "worktree /tmp/bare.git\x00bare\x00\x00"
    have hbList : sb.toList =
        "worktree /tmp/bare.git".toList ++ Char.ofNat 0 ::
        ("bare".toList ++ Char.ofNat 0 ::
        ("".toList ++ Char.ofNat 0 :: [])) := by decide
    have hToksB : splitNulTokensAllowEmptySpec [] sb.toList =
        some ["worktree /tmp/bare.git", "bare", ""] := by
      rw [hbList]
      rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
      rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
      rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
      have hNil : splitNulTokensAllowEmptySpec [] [] = some [] := rfl
      rw [hNil]
      simp only [List.reverse_nil, List.nil_append, String.ofList_toList, Option.map]
    have hStzB : splitWorktreeStanzasSpec [] ["worktree /tmp/bare.git", "bare", ""] =
        some [["worktree /tmp/bare.git", "bare"]] := by
      rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_tok _ _ _ (by decide)]
      rw [splitWorktreeStanzas_empty _ _ (by decide)]
      rfl
    have hPBare : parseWorktreeStanza ["worktree /tmp/bare.git", "bare"] =
        .ok { path := "/tmp/bare.git", head? := none, branch? := none, isBare := true } := by
      rw [parseWorktreeStanza_worktree "worktree /tmp/bare.git" "/tmp/bare.git" ["bare"] (by decide) (by decide)]
      rw [parseWorktreeAttrs_bare]
      rfl
    have hInfosB : parseWorktreeStanzasSpec [["worktree /tmp/bare.git", "bare"]] =
        .ok [{ path := "/tmp/bare.git", head? := none, branch? := none, isBare := true }] := by
      unfold parseWorktreeStanzasSpec
      rw [hPBare]
      rfl
    exact parseWorktreeListPorcelain_ok_of "worktree /tmp/bare.git\x00bare\x00\x00"
      ["worktree /tmp/bare.git", "bare", ""]
      [["worktree /tmp/bare.git", "bare"]]
      [{ path := "/tmp/bare.git", head? := none, branch? := none, isBare := true }]
      (toUTF8_nonempty_of_ne (by decide)) hToksB hStzB hInfosB
  refine ⟨hBare, ⟨?_, trivial⟩⟩
  let z40 := String.ofList (List.replicate 40 '0')
  let s := "worktree /tmp/wt\x00HEAD " ++ z40 ++ "\x00branch refs/heads/main\x00locked\x00prunable gone\x00\x00"
  have hEmptyFalse : s.toUTF8.isEmpty = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have he := (toUTF8_eq_empty_iff s).mp h
    have hl := congrArg String.length he
    simp [s] at hl
  have hHead : hasNulChar ("HEAD " ++ z40).toList = false :=
    hasNulChar_head_rep40 40 '0' (by decide)
  have h1 : "worktree /tmp/wt\x00HEAD ".toList =
      "worktree /tmp/wt".toList ++ Char.ofNat 0 :: "HEAD ".toList := by decide
  have h2 : "\x00branch refs/heads/main\x00locked\x00prunable gone\x00\x00".toList =
      Char.ofNat 0 :: ("branch refs/heads/main".toList ++ Char.ofNat 0 ::
      ("locked".toList ++ Char.ofNat 0 :: ("prunable gone".toList ++ Char.ofNat 0 :: ("".toList ++ Char.ofNat 0 :: [])))) := by decide
  have hsList : s.toList =
      "worktree /tmp/wt".toList ++ Char.ofNat 0 ::
      (("HEAD " ++ z40).toList ++ Char.ofNat 0 ::
      ("branch refs/heads/main".toList ++ Char.ofNat 0 ::
      ("locked".toList ++ Char.ofNat 0 ::
      ("prunable gone".toList ++ Char.ofNat 0 ::
      ("".toList ++ Char.ofNat 0 :: []))))) := by
    simp only [s, String.toList_append, h1, h2, List.append_assoc, List.cons_append]
  unfold parseWorktreeListPorcelain
  rw [hEmptyFalse, fromUTF8_toUTF8]
  dsimp only
  have hToks : splitNulTokensAllowEmptySpec [] s.toList =
      some ["worktree /tmp/wt", "HEAD " ++ z40, "branch refs/heads/main", "locked", "prunable gone", ""] := by
    rw [hsList]
    rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
    rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ hHead]
    rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
    rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
    rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
    rw [splitNulTokensAllowEmptyAux_append_nul _ _ _ (by decide)]
    have hNil : splitNulTokensAllowEmptySpec [] [] = some [] := rfl
    rw [hNil]
    simp only [List.reverse_nil, List.nil_append, String.ofList_toList, Option.map]
  let hzLine := "HEAD " ++ z40
  have hStz : splitWorktreeStanzasSpec []
      ["worktree /tmp/wt", hzLine, "branch refs/heads/main", "locked", "prunable gone", ""] =
      some [["worktree /tmp/wt", hzLine, "branch refs/heads/main", "locked", "prunable gone"]] := by
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_tok _ _ _ (head_str_ne_empty z40)]
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_tok _ _ _ (by decide)]
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_empty _ _ (by decide)]
    rfl
  have hRefMain : mkRefName "main" = .ok { raw := "main" } := by
    unfold mkRefName
    rw [show isValidRefNameStr "main" = true from by decide]
    rfl
  have hPWt : parseWorktreeStanza
      ["worktree /tmp/wt", hzLine, "branch refs/heads/main", "locked", "prunable gone"] =
      .ok { path := "/tmp/wt", head? := none, branch? := some { raw := "main" },
            isLocked := true, isPrunable := true, pruneReason := some "gone" } := by
    rw [parseWorktreeStanza_worktree "worktree /tmp/wt" "/tmp/wt"
      [hzLine, "branch refs/heads/main", "locked", "prunable gone"] (by decide) (by decide)]
    rw [parseWorktreeAttrs_head_zeros _ _ z40 _ isAllZeros_rep40_zero]
    rw [parseWorktreeAttrs_branch _ _ "branch refs/heads/main" "refs/heads/main" "main" { raw := "main" } _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hRefMain]
    rw [parseWorktreeAttrs_locked]
    rw [parseWorktreeAttrs_prunable_reason _ _ "prunable gone" "gone" _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    rfl
  have hInfos : parseWorktreeStanzasSpec
      [["worktree /tmp/wt", hzLine, "branch refs/heads/main", "locked", "prunable gone"]] =
      .ok [{ path := "/tmp/wt", head? := none, branch? := some { raw := "main" },
             isLocked := true, isPrunable := true, pruneReason := some "gone" }] := by
    unfold parseWorktreeStanzasSpec
    rw [hPWt]
    rfl
  rw [splitNulTokensAllowEmptyLoop_eq, hToks]
  dsimp only [Option.map, List.reverse_nil, List.nil_append]
  rw [splitWorktreeStanzasLoop_eq, hStz]
  dsimp only [Option.map, List.reverse_nil, List.nil_append]
  rw [parseWorktreeStanzasLoop_eq, hInfos]
  rfl


/-- Proof of `test_git_status_parsesRealOutput` for `parsePorcelainStatusZ`. -/
theorem proof_test_git_status_parsesRealOutput :
    AllPass (test_git_status_parsesRealOutput parsePorcelainStatusZ) := by
  dsimp only [test_git_status_parsesRealOutput, AllPass, assert]
  refine ⟨?_, trivial⟩
  let s := " M a b.txt\x00R  new name.txt\x00old name.txt\x00?? untrack.txt\x00"
  have hsList : s.toList =
      " M a b.txt".toList ++ Char.ofNat 0 ::
      ("R  new name.txt".toList ++ Char.ofNat 0 ::
      ("old name.txt".toList ++ Char.ofNat 0 ::
      ("?? untrack.txt".toList ++ Char.ofNat 0 :: []))) := by decide
  have h4 : splitNulRecordsSpec [] ("?? untrack.txt".toList ++ Char.ofNat 0 :: []) = some ["?? untrack.txt"] :=
    splitNulRecordsAux_step "?? untrack.txt" [] [] (by decide) (by decide) rfl
  have h3 := splitNulRecordsAux_step "old name.txt" _ _ (by decide) (by decide) h4
  have h2 := splitNulRecordsAux_step "R  new name.txt" _ _ (by decide) (by decide) h3
  have h1 := splitNulRecordsAux_step " M a b.txt" _ _ (by decide) (by decide) h2
  have hToks : splitNulRecordsSpec [] s.toList =
      some [" M a b.txt", "R  new name.txt", "old name.txt", "?? untrack.txt"] := by
    rw [hsList]; exact h1
  have hRecs : parsePorcelainStatusSpec
      [" M a b.txt", "R  new name.txt", "old name.txt", "?? untrack.txt"] =
      .ok [ { indexStatus := none, worktreeStatus := some .modified, path := "a b.txt" },
            { indexStatus := some .renamed, worktreeStatus := none, path := "new name.txt", origPath := some "old name.txt" },
            { indexStatus := some .untracked, worktreeStatus := some .untracked, path := "untrack.txt" } ] := by
    have hr3 : parsePorcelainStatusSpec ["?? untrack.txt"] =
        .ok [{ indexStatus := some .untracked, worktreeStatus := some .untracked, path := "untrack.txt" }] := by
      rw [parsePorcelainStatusRecords_plain "?? untrack.txt" "untrack.txt" '?' '?' [] (some .untracked) (some .untracked)
        (by decide) (by decide) (by decide) rfl rfl ⟨by decide, by decide⟩ ⟨by decide, by decide⟩]
      rfl
    have hr2 : parsePorcelainStatusSpec ["R  new name.txt", "old name.txt", "?? untrack.txt"] =
        .ok [ { indexStatus := some .renamed, worktreeStatus := none, path := "new name.txt", origPath := some "old name.txt" },
              { indexStatus := some .untracked, worktreeStatus := some .untracked, path := "untrack.txt" } ] := by
      rw [parsePorcelainStatusRecords_rc "R  new name.txt" "new name.txt" "old name.txt" 'R' ' ' ["?? untrack.txt"]
        (some .renamed) none (by decide) (by decide) (by decide) rfl rfl (by decide), hr3]
      rfl
    rw [parsePorcelainStatusRecords_plain " M a b.txt" "a b.txt" ' ' 'M'
      ["R  new name.txt", "old name.txt", "?? untrack.txt"] none (some .modified)
      (by decide) (by decide) (by decide) rfl rfl ⟨by decide, by decide⟩ ⟨by decide, by decide⟩, hr2]
    rfl
  exact parsePorcelainStatusZ_ok_of s _ _ (toUTF8_nonempty_of_ne (by decide)) hToks hRecs

/-- Proof of `test_git_worktreeList_parsesRealOutput` for `parseWorktreeListPorcelain`. -/
theorem proof_test_git_worktreeList_parsesRealOutput :
    AllPass (test_git_worktreeList_parsesRealOutput parseWorktreeListPorcelain) := by
  dsimp only [test_git_worktreeList_parsesRealOutput, AllPass, assert]
  refine ⟨?_, trivial⟩
  let sha := String.ofList (List.replicate 40 'a')
  let s := "worktree /tmp/main\x00HEAD " ++ sha ++ "\x00branch refs/heads/main\x00\x00worktree /tmp/wt\x00HEAD " ++ sha ++ "\x00detached\x00\x00"
  have hEmptyFalse : s.toUTF8.isEmpty = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have he := (toUTF8_eq_empty_iff s).mp h
    have hl := congrArg String.length he
    simp [s] at hl
  have hHead : hasNulChar ("HEAD " ++ sha).toList = false :=
    hasNulChar_head_rep40 40 'a' (by decide)
  have h1 : "worktree /tmp/main\x00HEAD ".toList =
      "worktree /tmp/main".toList ++ Char.ofNat 0 :: "HEAD ".toList := by decide
  have h2 : "\x00branch refs/heads/main\x00\x00worktree /tmp/wt\x00HEAD ".toList =
      Char.ofNat 0 :: ("branch refs/heads/main".toList ++ Char.ofNat 0 ::
      ("".toList ++ Char.ofNat 0 :: ("worktree /tmp/wt".toList ++ Char.ofNat 0 :: "HEAD ".toList))) := by decide
  have h3 : "\x00detached\x00\x00".toList =
      Char.ofNat 0 :: ("detached".toList ++ Char.ofNat 0 :: ("".toList ++ Char.ofNat 0 :: [])) := by decide
  have hsList : s.toList =
      "worktree /tmp/main".toList ++ Char.ofNat 0 ::
      (("HEAD " ++ sha).toList ++ Char.ofNat 0 ::
      ("branch refs/heads/main".toList ++ Char.ofNat 0 ::
      ("".toList ++ Char.ofNat 0 ::
      ("worktree /tmp/wt".toList ++ Char.ofNat 0 ::
      (("HEAD " ++ sha).toList ++ Char.ofNat 0 ::
      ("detached".toList ++ Char.ofNat 0 ::
      ("".toList ++ Char.ofNat 0 :: []))))))) := by
    simp only [s, String.toList_append, h1, h2, h3, List.append_assoc, List.cons_append]
  have ht8 : splitNulTokensAllowEmptySpec [] ("".toList ++ Char.ofNat 0 :: []) = some [""] :=
    splitNulTokensAllowEmptyAux_step "" [] [] (by decide) rfl
  have ht7 := splitNulTokensAllowEmptyAux_step "detached" _ _ (by decide) ht8
  have ht6 := splitNulTokensAllowEmptyAux_step ("HEAD " ++ sha) _ _ hHead ht7
  have ht5 := splitNulTokensAllowEmptyAux_step "worktree /tmp/wt" _ _ (by decide) ht6
  have ht4 := splitNulTokensAllowEmptyAux_step "" _ _ (by decide) ht5
  have ht3 := splitNulTokensAllowEmptyAux_step "branch refs/heads/main" _ _ (by decide) ht4
  have ht2 := splitNulTokensAllowEmptyAux_step ("HEAD " ++ sha) _ _ hHead ht3
  have ht1 := splitNulTokensAllowEmptyAux_step "worktree /tmp/main" _ _ (by decide) ht2
  have hToks : splitNulTokensAllowEmptySpec [] s.toList =
      some ["worktree /tmp/main", "HEAD " ++ sha, "branch refs/heads/main", "", "worktree /tmp/wt", "HEAD " ++ sha, "detached", ""] := by
    rw [hsList]; exact ht1
  let haLine := "HEAD " ++ sha
  have hCidA : mkCommitId sha = .ok { hex := sha } := by
    unfold mkCommitId
    rw [isValidCommitIdStr_rep40_a]
    rfl
  have hRefMain : mkRefName "main" = .ok { raw := "main" } := by
    unfold mkRefName
    rw [show isValidRefNameStr "main" = true from by decide]
    rfl
  have hStz : splitWorktreeStanzasSpec []
      ["worktree /tmp/main", haLine, "branch refs/heads/main", "", "worktree /tmp/wt", haLine, "detached", ""] =
      some [["worktree /tmp/main", haLine, "branch refs/heads/main"],
            ["worktree /tmp/wt", haLine, "detached"]] := by
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_tok _ _ _ (head_str_ne_empty sha)]
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_empty _ _ (by decide)]
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_tok _ _ _ (head_str_ne_empty sha)]
    rw [splitWorktreeStanzas_tok _ _ _ (by decide), splitWorktreeStanzas_empty _ _ (by decide)]
    rfl
  have hP1 : parseWorktreeStanza ["worktree /tmp/main", haLine, "branch refs/heads/main"] =
      .ok { path := "/tmp/main", head? := some { hex := sha }, branch? := some { raw := "main" } } := by
    rw [parseWorktreeStanza_worktree "worktree /tmp/main" "/tmp/main"
      [haLine, "branch refs/heads/main"] (by decide) (by decide)]
    rw [parseWorktreeAttrs_head_commit _ _ sha { hex := sha } _ isAllZeros_rep40_a hCidA]
    rw [parseWorktreeAttrs_branch _ _ "branch refs/heads/main" "refs/heads/main" "main" { raw := "main" } _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hRefMain]
    rfl
  have hP2 : parseWorktreeStanza ["worktree /tmp/wt", haLine, "detached"] =
      .ok { path := "/tmp/wt", head? := some { hex := sha }, branch? := none, isDetached := true } := by
    rw [parseWorktreeStanza_worktree "worktree /tmp/wt" "/tmp/wt"
      [haLine, "detached"] (by decide) (by decide)]
    rw [parseWorktreeAttrs_head_commit _ _ sha { hex := sha } _ isAllZeros_rep40_a hCidA]
    rw [parseWorktreeAttrs_detached]
    rfl
  have hInfos : parseWorktreeStanzasSpec
      [["worktree /tmp/main", haLine, "branch refs/heads/main"],
       ["worktree /tmp/wt", haLine, "detached"]] =
      .ok [{ path := "/tmp/main", head? := some { hex := sha }, branch? := some { raw := "main" } },
           { path := "/tmp/wt", head? := some { hex := sha }, branch? := none, isDetached := true }] := by
    unfold parseWorktreeStanzasSpec
    rw [hP1]
    dsimp only [bind, Except.bind, pure, Except.pure]
    unfold parseWorktreeStanzasSpec
    rw [hP2]
    rfl
  exact parseWorktreeListPorcelain_ok_of s _ _ _ hEmptyFalse hToks hStz hInfos

end LeanSwe.Git.Proofs

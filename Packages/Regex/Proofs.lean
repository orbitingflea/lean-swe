import Packages.Regex.Impl
import Packages.Regex.SpecTests

/-!
# Regex Proofs

Machine-checked proofs discharging every `AllPass` safety specification and
`CanReach` non-vacuity witness for `Packages.Regex.liveApi`.
-/

namespace Packages.Regex.Proofs

open Core
open Core.NondetTest

private theorem error_toString_ne_empty (err : _root_.Regex.Syntax.Parser.Error) :
    toString err ≠ "" := by
  cases err <;> simp [toString]

/-- Proof of `test_regex_onError_returnsNonEmptyMessage` for `liveApi`. -/
theorem proof_regex_onError_returnsNonEmptyMessage :
    AllPass (test_regex_onError_returnsNonEmptyMessage liveApi) := by
  intro pat hay
  simp only [liveApi, compilePattern]
  cases hp : _root_.Regex.parse pat with
  | ok _ => simp [bind, Except.bind, pure, Except.pure, assume]
  | error err =>
    simp only [bind, Except.bind, mapError, assert]
    exact ⟨error_toString_ne_empty err, trivial⟩

/-- Proof of `test_regex_testPattern_iff_findFirstSome` for `liveApi`. -/
theorem proof_regex_testPattern_iff_findFirstSome :
    AllPass (test_regex_testPattern_iff_findFirstSome liveApi) := by
  intro pat hay
  simp only [liveApi, compilePattern]
  cases hp : _root_.Regex.parse pat with
  | error _ => simp [bind, Except.bind, assume]
  | ok re =>
    simp only [bind, Except.bind, pure, Except.pure, _root_.Regex.test, Option.isSome_map, assert]
    exact ⟨by simp, trivial⟩

/-- Proof of `test_regex_countMatches_eq_findAllSize` for `liveApi`. -/
theorem proof_regex_countMatches_eq_findAllSize :
    AllPass (test_regex_countMatches_eq_findAllSize liveApi) := by
  intro pat hay
  simp only [liveApi, compilePattern]
  cases hp : _root_.Regex.parse pat with
  | error _ => simp [bind, Except.bind, assume]
  | ok re =>
    simp only [bind, Except.bind, pure, Except.pure, _root_.Regex.count, Array.size_map, assert]
    trivial

private theorem findAll_go_str_eq {hay : String} (m : _root_.Regex.Matches hay)
    (accum : Array String.Slice) (hacc : ∀ s ∈ accum, s.str = hay) :
    ∀ s ∈ _root_.Regex.findAll.go hay m accum, s.str = hay := by
  induction m, accum using _root_.Regex.findAll.go.induct with
  | case1 m accum slice m' hnext ih =>
    rw [_root_.Regex.findAll.go, hnext]
    apply ih
    intro s hs
    simp only [Array.mem_push] at hs
    rcases hs with hm | rfl
    · exact hacc s hm
    · exact _root_.Regex.Matches.str_eq_of_next?_some hnext
  | case2 m accum hnext =>
    rw [_root_.Regex.findAll.go, hnext]
    exact hacc

/-- Proof of `test_regex_findAll_spansValid` for `liveApi`. -/
theorem proof_regex_findAll_spansValid :
    AllPass (test_regex_findAll_spansValid liveApi) := by
  intro pat hay
  simp only [liveApi, compilePattern]
  cases hp : _root_.Regex.parse pat with
  | error _ => simp [bind, Except.bind, assume]
  | ok re =>
    intro i hi
    simp only [Array.size_map] at hi
    have hmap : i < (Array.map sliceToSpan (re.findAll hay)).size := by
      simpa [Array.size_map] using hi
    have hget : (Array.map sliceToSpan (re.findAll hay))[i]! =
        sliceToSpan ((re.findAll hay)[i]'hi) := by
      rw [getElem!_pos (Array.map sliceToSpan (re.findAll hay)) i hmap]
      simp
    simp only [hget, sliceToSpan, assert]
    let sl : String.Slice := (re.findAll hay)[i]'hi
    have hslMem : sl ∈ re.findAll hay := Array.getElem_mem hi
    have hstr : sl.str = hay := by
      unfold _root_.Regex.findAll at hslMem
      exact findAll_go_str_eq (re.matches hay) #[] (by intro s hs; simp at hs) sl hslMem
    refine ⟨⟨sl.startInclusive_le_endExclusive, ?_⟩, trivial⟩
    simpa [hstr] using sl.endExclusive.isValid.le_utf8ByteSize

private theorem split_go_size_ge_one {hay : String} (m : _root_.Regex.Matches hay)
    (accum : Array String.Slice) (endPos : String.Pos hay) :
    1 ≤ (_root_.Regex.split.go hay m accum endPos).size := by
  induction m, accum, endPos using _root_.Regex.split.go.induct with
  | case1 m accum endPos s m' hnext _ startPos le ih =>
    rw [_root_.Regex.split.go]
    split
    · next s' m'' heq =>
      rw [hnext] at heq
      injection heq with hpair
      have hs : s = s' := congrArg Prod.fst hpair
      have hm : m' = m'' := congrArg Prod.snd hpair
      subst hs; subst hm
      dsimp only
      rw [dif_pos le]
      exact ih
    · next heq => rw [hnext] at heq; contradiction
  | case2 m accum endPos s m' hnext _ startPos nle ih =>
    rw [_root_.Regex.split.go]
    split
    · next s' m'' heq =>
      rw [hnext] at heq
      injection heq with hpair
      have hs : s = s' := congrArg Prod.fst hpair
      have hm : m' = m'' := congrArg Prod.snd hpair
      subst hs; subst hm
      dsimp only
      rw [dif_neg nle]
      exact ih
    · next heq => rw [hnext] at heq; contradiction
  | case3 m accum endPos hnext =>
    rw [_root_.Regex.split.go]
    split
    · next heq => simp [hnext] at heq
    · simp

/-- Proof of `test_regex_splitBy_nonEmpty` for `liveApi`. -/
theorem proof_regex_splitBy_nonEmpty :
    AllPass (test_regex_splitBy_nonEmpty liveApi) := by
  intro pat hay
  simp only [liveApi, compilePattern]
  cases hp : _root_.Regex.parse pat with
  | error _ => simp [bind, Except.bind, assume]
  | ok re =>
    simp only [bind, Except.bind, pure, Except.pure, _root_.Regex.split, Array.size_map, assert]
    exact ⟨split_go_size_ge_one (re.matches hay) #[] hay.startPos, trivial⟩

private theorem parseAst_empty_eq :
    _root_.Regex.Syntax.Parser.parseAst "" = .ok .epsilon := by
  have hne : ¬ ("".startPos ≠ "".endPos) := by decide
  have hend : ("".startPos == "".endPos) = true := by decide
  unfold _root_.Regex.Syntax.Parser.parseAst
  rw [_root_.Regex.Syntax.Parser.regex.eq_def, _root_.Regex.Syntax.Parser.alternate.eq_def,
    _root_.Regex.Syntax.Parser.concat.eq_def, _root_.Regex.Syntax.Parser.repetition.eq_def,
    _root_.Regex.Syntax.Parser.primary.eq_def]
  simp only [_root_.Regex.Syntax.Parser.group, _root_.Regex.Syntax.Parser.classes,
    _root_.Regex.Syntax.Parser.characterClasses, _root_.Regex.Syntax.Parser.dot,
    _root_.Regex.Syntax.Parser.anchor, _root_.Regex.Syntax.Parser.escapedChar,
    _root_.Regex.Syntax.Parser.plainChar, _root_.Regex.Syntax.Parser.charOrError,
    _root_.Regex.Syntax.Parser.anyCharOrError, _root_.Regex.Syntax.Parser.Combinators.charOrElse,
    _root_.Regex.Syntax.Parser.Combinators.anyCharOrElse,
    _root_.Regex.Syntax.Parser.Combinators.Parser.mapConst,
    _root_.Regex.Syntax.Parser.Combinators.Parser.guard,
    _root_.Regex.Syntax.Parser.Combinators.Parser.seqRight,
    _root_.Regex.Syntax.Parser.Combinators.Parser.orElse,
    _root_.Regex.Syntax.Parser.Combinators.Result.guard,
    _root_.Regex.Syntax.Parser.Combinators.Result.map,
    _root_.Regex.Syntax.Parser.Combinators.Result.map',
    _root_.Regex.Syntax.Parser.Combinators.Result.bind',
    _root_.Regex.Syntax.Parser.Combinators.Result.cast,
    _root_.Regex.Syntax.Parser.Combinators.Result.imp,
    _root_.Regex.Syntax.Parser.Combinators.Result.weaken,
    _root_.Regex.Syntax.Parser.Combinators.Result.pure,
    _root_.Regex.Syntax.Parser.Combinators.Result.orElse,
    _root_.Regex.Syntax.Parser.Combinators.Result.hOrElse,
    _root_.Regex.Syntax.Parser.Combinators.Result.transOr,
    _root_.Regex.Syntax.Parser.Combinators.Result.complete,
    _root_.Regex.Syntax.Parser.Combinators.Result.toExcept,
    HOrElse.hOrElse, OrElse.orElse, Pure.pure, Functor.map, Functor.mapConst,
    SeqRight.seqRight, Function.comp_apply, hne, ↓reduceDIte]
  rw [_root_.Regex.Syntax.Parser.alternate1.eq_def]
  simp only [_root_.Regex.Syntax.Parser.charOrError,
    _root_.Regex.Syntax.Parser.Combinators.charOrElse,
    _root_.Regex.Syntax.Parser.Combinators.anyCharOrElse,
    _root_.Regex.Syntax.Parser.Combinators.Result.guard,
    _root_.Regex.Syntax.Parser.Combinators.Result.bind',
    _root_.Regex.Syntax.Parser.Combinators.Result.pure,
    _root_.Regex.Syntax.Parser.Combinators.Result.imp,
    _root_.Regex.Syntax.Parser.Combinators.Result.weaken,
    _root_.Regex.Syntax.Parser.Combinators.Result.hOrElse,
    HOrElse.hOrElse, Pure.pure, hne, ↓reduceDIte, hend, ↓reduceIte]

private theorem hne_lbracket : "[".startPos ≠ "[".endPos := by decide
private theorem hch_lbracket : "[".startPos.get hne_lbracket = '[' := by decide
private theorem hnxt_lbracket : "[".startPos.next hne_lbracket = "[".endPos := by decide

private theorem parseAst_lbracket_eq :
    _root_.Regex.Syntax.Parser.parseAst "[" = .error .unexpectedEof := by
  have hne1 : ¬ ("[".endPos ≠ "[".endPos) := by decide
  have hc1 : '(' ≠ '[' := by decide
  unfold _root_.Regex.Syntax.Parser.parseAst
  rw [_root_.Regex.Syntax.Parser.regex.eq_def, _root_.Regex.Syntax.Parser.alternate.eq_def,
    _root_.Regex.Syntax.Parser.concat.eq_def, _root_.Regex.Syntax.Parser.repetition.eq_def,
    _root_.Regex.Syntax.Parser.primary.eq_def]
  simp only [_root_.Regex.Syntax.Parser.group, _root_.Regex.Syntax.Parser.classes,
    _root_.Regex.Syntax.Parser.characterClasses, _root_.Regex.Syntax.Parser.charOrError,
    _root_.Regex.Syntax.Parser.Combinators.charOrElse,
    _root_.Regex.Syntax.Parser.Combinators.anyCharOrElse,
    _root_.Regex.Syntax.Parser.Combinators.testP, _root_.Regex.Syntax.Parser.Combinators.test,
    _root_.Regex.Syntax.Parser.Combinators.Result.guard,
    _root_.Regex.Syntax.Parser.Combinators.Result.commit,
    _root_.Regex.Syntax.Parser.Combinators.Result.map,
    _root_.Regex.Syntax.Parser.Combinators.Result.map',
    _root_.Regex.Syntax.Parser.Combinators.Result.bind',
    _root_.Regex.Syntax.Parser.Combinators.Result.bind,
    _root_.Regex.Syntax.Parser.Combinators.Result.cast,
    _root_.Regex.Syntax.Parser.Combinators.Result.imp,
    _root_.Regex.Syntax.Parser.Combinators.Result.weaken,
    _root_.Regex.Syntax.Parser.Combinators.Result.pure,
    _root_.Regex.Syntax.Parser.Combinators.Result.orElse,
    _root_.Regex.Syntax.Parser.Combinators.Result.hOrElse,
    _root_.Regex.Syntax.Parser.Combinators.Result.transOr,
    _root_.Regex.Syntax.Parser.Combinators.Result.complete,
    _root_.Regex.Syntax.Parser.Combinators.Result.toExcept,
    HOrElse.hOrElse, OrElse.orElse, Pure.pure, Functor.map,
    dif_pos hne_lbracket, hch_lbracket, hnxt_lbracket, dif_neg hne1, hc1,
    ↓reduceIte, Bool.false_eq_true]
  rw [_root_.Regex.Syntax.Parser.classesSeq.eq_def,
    _root_.Regex.Syntax.Parser.classesItem.eq_def,
    _root_.Regex.Syntax.Parser.classesAtom.eq_def]
  simp only [_root_.Regex.Syntax.Parser.characterClasses,
    _root_.Regex.Syntax.Parser.singleClass, _root_.Regex.Syntax.Parser.range,
    _root_.Regex.Syntax.Parser.charInClass, _root_.Regex.Syntax.Parser.escapedChar,
    _root_.Regex.Syntax.Parser.charOrError, _root_.Regex.Syntax.Parser.anyCharOrError,
    _root_.Regex.Syntax.Parser.Combinators.charOrElse,
    _root_.Regex.Syntax.Parser.Combinators.anyCharOrElse,
    _root_.Regex.Syntax.Parser.Combinators.Parser.guard,
    _root_.Regex.Syntax.Parser.Combinators.Parser.map,
    _root_.Regex.Syntax.Parser.Combinators.Parser.commit,
    _root_.Regex.Syntax.Parser.Combinators.Parser.orElse,
    _root_.Regex.Syntax.Parser.Combinators.Parser.seqRight,
    _root_.Regex.Syntax.Parser.Combinators.Result.bind',
    _root_.Regex.Syntax.Parser.Combinators.Result.commit,
    _root_.Regex.Syntax.Parser.Combinators.Result.map,
    _root_.Regex.Syntax.Parser.Combinators.Result.guard,
    _root_.Regex.Syntax.Parser.Combinators.Result.imp,
    _root_.Regex.Syntax.Parser.Combinators.Result.weaken,
    _root_.Regex.Syntax.Parser.Combinators.Result.hOrElse,
    _root_.Regex.Syntax.Parser.Combinators.Result.transOr,
    HOrElse.hOrElse, OrElse.orElse, Functor.map, SeqRight.seqRight, dif_neg hne1]
  rfl

private theorem parse_empty_ok :
    _root_.Regex.parse "" = .ok (_root_.Regex.fromExpr (.group 0 .epsilon)) := by
  unfold _root_.Regex.parse _root_.Regex.parseAux _root_.Regex.Syntax.Parser.parseAux
  simp [parseAst_empty_eq, Functor.map, Except.map, _root_.Regex.Syntax.Parser.Ast.toRegexAux]

private theorem parse_lbracket_err :
    _root_.Regex.parse "[" = .error .unexpectedEof := by
  unfold _root_.Regex.parse _root_.Regex.parseAux _root_.Regex.Syntax.Parser.parseAux
  simp [parseAst_lbracket_eq, Functor.map, Except.map]

private theorem pushNext_save {s : String} (σ : _root_.Regex.Strategy s) (nfa : _root_.Regex.NFA)
    (p : String.Pos s) (node : _root_.Regex.NFA.Node) (hin : node.inBounds nfa.nodes.size)
    (u : σ.Update) (stk : _root_.Regex.VM.εStack σ nfa) (off next : Nat)
    (hnode : node = .save off next) :
    _root_.Regex.VM.εClosure.pushNext σ nfa p node hin u stk =
      (σ.write u off p, ⟨next, by subst hnode; exact hin⟩) :: stk := by
  subst hnode; rfl

private theorem pushNext_epsilon {s : String} (σ : _root_.Regex.Strategy s) (nfa : _root_.Regex.NFA)
    (p : String.Pos s) (node : _root_.Regex.NFA.Node) (hin : node.inBounds nfa.nodes.size)
    (u : σ.Update) (stk : _root_.Regex.VM.εStack σ nfa) (next : Nat)
    (hnode : node = .epsilon next) :
    _root_.Regex.VM.εClosure.pushNext σ nfa p node hin u stk =
      (u, ⟨next, by subst hnode; exact hin⟩) :: stk := by
  subst hnode; rfl

private theorem pushNext_done {s : String} (σ : _root_.Regex.Strategy s) (nfa : _root_.Regex.NFA)
    (p : String.Pos s) (node : _root_.Regex.NFA.Node) (hin : node.inBounds nfa.nodes.size)
    (u : σ.Update) (stk : _root_.Regex.VM.εStack σ nfa) (hnode : node = .done) :
    _root_.Regex.VM.εClosure.pushNext σ nfa p node hin u stk = stk := by
  subst hnode; rfl

private theorem εClosure_save {s : String} (σ : _root_.Regex.Strategy s) (nfa : _root_.Regex.NFA)
    (wf : nfa.WellFormed) (p : String.Pos s) (matched : Option σ.Update)
    (st : _root_.Regex.VM.SearchState σ nfa) (u : σ.Update) (state : Fin nfa.nodes.size)
    (stk : _root_.Regex.VM.εStack σ nfa) (hmem : ¬ state ∈ st.states) (off next : Nat)
    (hnode : nfa[state] = .save off next) :
    _root_.Regex.VM.εClosure σ nfa wf p matched st ((u, state) :: stk) =
      _root_.Regex.VM.εClosure σ nfa wf p matched ⟨st.states.insert state hmem, st.updates⟩
        ((σ.write u off p, ⟨next, by simpa [hnode] using wf.inBounds state⟩) :: stk) := by
  rw [_root_.Regex.VM.εClosure.eq_def]; dsimp only
  rw [dif_neg hmem]
  have h1 : (nfa[state]).isDone = false := by simp [hnode, _root_.Regex.NFA.Node.isDone]
  have h2 : _root_.Regex.VM.εClosure.writeUpdate nfa[state] = false := by
    simp [hnode, _root_.Regex.VM.εClosure.writeUpdate]
  rw [h1, h2, pushNext_save σ nfa p nfa[state] _ u stk off next hnode]
  rfl

private theorem εClosure_epsilon {s : String} (σ : _root_.Regex.Strategy s) (nfa : _root_.Regex.NFA)
    (wf : nfa.WellFormed) (p : String.Pos s) (matched : Option σ.Update)
    (st : _root_.Regex.VM.SearchState σ nfa) (u : σ.Update) (state : Fin nfa.nodes.size)
    (stk : _root_.Regex.VM.εStack σ nfa) (hmem : ¬ state ∈ st.states) (next : Nat)
    (hnode : nfa[state] = .epsilon next) :
    _root_.Regex.VM.εClosure σ nfa wf p matched st ((u, state) :: stk) =
      _root_.Regex.VM.εClosure σ nfa wf p matched ⟨st.states.insert state hmem, st.updates⟩
        ((u, ⟨next, by simpa [hnode] using wf.inBounds state⟩) :: stk) := by
  rw [_root_.Regex.VM.εClosure.eq_def]; dsimp only
  rw [dif_neg hmem]
  have h1 : (nfa[state]).isDone = false := by simp [hnode, _root_.Regex.NFA.Node.isDone]
  have h2 : _root_.Regex.VM.εClosure.writeUpdate nfa[state] = false := by
    simp [hnode, _root_.Regex.VM.εClosure.writeUpdate]
  rw [h1, h2, pushNext_epsilon σ nfa p nfa[state] _ u stk next hnode]
  rfl

private theorem εClosure_done {s : String} (σ : _root_.Regex.Strategy s) (nfa : _root_.Regex.NFA)
    (wf : nfa.WellFormed) (p : String.Pos s) (matched : Option σ.Update)
    (st : _root_.Regex.VM.SearchState σ nfa) (u : σ.Update) (state : Fin nfa.nodes.size)
    (stk : _root_.Regex.VM.εStack σ nfa) (hmem : ¬ state ∈ st.states)
    (hnode : nfa[state] = .done) :
    _root_.Regex.VM.εClosure σ nfa wf p matched st ((u, state) :: stk) =
      _root_.Regex.VM.εClosure σ nfa wf p (matched <|> some u)
        ⟨st.states.insert state hmem, st.updates.set state u⟩ stk := by
  rw [_root_.Regex.VM.εClosure.eq_def]; dsimp only
  rw [dif_neg hmem]
  have h1 : (nfa[state]).isDone = true := by simp [hnode, _root_.Regex.NFA.Node.isDone]
  have h2 : _root_.Regex.VM.εClosure.writeUpdate nfa[state] = true := by
    simp [hnode, _root_.Regex.VM.εClosure.writeUpdate]
  rw [h1, h2, pushNext_done σ nfa p nfa[state] _ u stk hnode]
  rfl

private theorem vm_empty_val :
    let nfa := _root_.Regex.NFA.compile (.group 0 .epsilon)
    (_root_.Regex.VM.captureNextBuf nfa _root_.Regex.NFA.compile_wf 2 "".startPos) =
      some ((_root_.Regex.Buffer.empty (s := "") (size := 2)).setIfInBounds 0 (String.PosPlusOne.pos "".startPos)
        |>.setIfInBounds 1 (String.PosPlusOne.pos "".startPos)) := by
  have heq : "".startPos = "".endPos := by decide
  let nfa0 : _root_.Regex.NFA :=
    { nodes := #[.done, .save 1 0, .epsilon 1, .save 0 2], start := 3 }
  have hnfa : _root_.Regex.NFA.compile (.group 0 .epsilon) = nfa0 := by decide
  dsimp only
  simp only [hnfa]
  unfold _root_.Regex.VM.captureNextBuf
  rw [_root_.Regex.VM.captureNext.eq_def]
  have hgo : ∀ m cur nxt, _root_.Regex.VM.captureNext.go (_root_.Regex.BufferStrategy "" 2) nfa0
      (hnfa ▸ _root_.Regex.NFA.compile_wf) "".startPos m cur nxt = m := by
    intro m cur nxt
    rw [_root_.Regex.VM.captureNext.go.eq_def]
    simp [heq]
  simp only [hgo]
  have h3 : nfa0[(⟨3, by decide⟩ : Fin nfa0.nodes.size)] = _root_.Regex.NFA.Node.save 0 2 := rfl
  have h2 : nfa0[(⟨2, by decide⟩ : Fin nfa0.nodes.size)] = _root_.Regex.NFA.Node.epsilon 1 := rfl
  have h1 : nfa0[(⟨1, by decide⟩ : Fin nfa0.nodes.size)] = _root_.Regex.NFA.Node.save 1 0 := rfl
  have h0 : nfa0[(⟨0, by decide⟩ : Fin nfa0.nodes.size)] = _root_.Regex.NFA.Node.done := rfl
  rw [εClosure_save (off := 0) (next := 2) (hmem := by clear heq hnfa hgo; decide) (hnode := h3)]
  rw [εClosure_epsilon (next := 1) (hmem := by clear heq hnfa hgo; decide) (hnode := h2)]
  rw [εClosure_save (off := 1) (next := 0) (hmem := by clear heq hnfa hgo; decide) (hnode := h1)]
  rw [εClosure_done (hmem := by clear heq hnfa hgo; decide) (hnode := h0)]
  rw [_root_.Regex.VM.εClosure.eq_def]
  rfl

private theorem findAll_go_size_mono {hay : String} (m : _root_.Regex.Matches hay)
    (accum : Array String.Slice) :
    accum.size ≤ (_root_.Regex.findAll.go hay m accum).size := by
  induction m, accum using _root_.Regex.findAll.go.induct with
  | case1 m accum slice m' hnext ih =>
    rw [_root_.Regex.findAll.go, hnext]
    exact Nat.le_trans (by simp) ih
  | case2 m accum hnext =>
    rw [_root_.Regex.findAll.go, hnext]
    exact Nat.le_refl _

private def nfaEmpty : _root_.Regex.NFA :=
  { nodes := #[.done, .save 1 0, .epsilon 1, .save 0 2], start := 3 }

private theorem nfaEmpty_eq : _root_.Regex.NFA.compile (.group 0 .epsilon) = nfaEmpty := by decide

private theorem stepChar_nfaEmpty_none {s : String} (σ : _root_.Regex.Strategy s)
    (wf : nfaEmpty.WellFormed) (p : String.Pos s) (ne : p ≠ s.endPos)
    (u : Vector σ.Update nfaEmpty.nodes.size) (nxt : _root_.Regex.VM.SearchState σ nfaEmpty)
    (state : Fin nfaEmpty.nodes.size) :
    (_root_.Regex.VM.stepChar σ nfaEmpty wf p ne u nxt state).1 = none := by
  unfold _root_.Regex.VM.stepChar
  rcases state with ⟨k, hk⟩
  have hk4 : k < 4 := hk
  match k with
  | 0 | 1 | 2 | 3 => rfl
  | _ + 4 => omega

private theorem eachStepChar_go_nfaEmpty_none {s : String} (σ : _root_.Regex.Strategy s)
    (wf : nfaEmpty.WellFormed) (p : String.Pos s) (ne : p ≠ s.endPos)
    (cur nxt : _root_.Regex.VM.SearchState σ nfaEmpty) (i : Nat) (hle : i ≤ cur.states.count) :
    (_root_.Regex.VM.eachStepChar.go σ nfaEmpty wf p ne cur i hle nxt).1 = none := by
  rw [_root_.Regex.VM.eachStepChar.go.eq_def]
  split
  · rfl
  · dsimp only
    split
    · rfl
    · have hst := stepChar_nfaEmpty_none σ wf p ne cur.updates nxt cur.states[i]
      have his : (_root_.Regex.VM.stepChar σ nfaEmpty wf p ne cur.updates nxt cur.states[i]).1.isSome =
          false := by
        simp [hst]
      rw [his]
      exact eachStepChar_go_nfaEmpty_none σ wf p ne cur
        (_root_.Regex.VM.stepChar σ nfaEmpty wf p ne cur.updates nxt cur.states[i]).2 (i + 1) _
termination_by cur.states.count - i

private theorem captureNext_go_some_const {s : String} (σ : _root_.Regex.Strategy s)
    (wf : nfaEmpty.WellFormed) (p : String.Pos s) (u : σ.Update)
    (cur nxt : _root_.Regex.VM.SearchState σ nfaEmpty) :
    _root_.Regex.VM.captureNext.go σ nfaEmpty wf p (some u) cur nxt = some u := by
  rw [_root_.Regex.VM.captureNext.go.eq_def]
  split
  · rfl
  · next hne =>
    split
    · rfl
    · have he := eachStepChar_go_nfaEmpty_none σ wf p hne cur nxt 0 (Nat.zero_le _)
      have he' : (_root_.Regex.VM.eachStepChar σ nfaEmpty wf p hne cur nxt).1 = none := he
      dsimp only
      rw [he']
      have hor : (none <|> some u) = some u := rfl
      rw [hor]
      exact captureNext_go_some_const σ wf (p.next hne) u
        (_root_.Regex.VM.eachStepChar σ nfaEmpty wf p hne cur nxt).2
        { states := cur.states.clear, updates := cur.updates }
termination_by p

private theorem nfaEmpty_mem3 :
    ¬ (⟨3, by decide⟩ : Fin nfaEmpty.nodes.size) ∈ _root_.Regex.Data.SparseSet.empty := by
  decide

private theorem nfaEmpty_mem2 :
    ¬ (⟨2, by decide⟩ : Fin nfaEmpty.nodes.size) ∈
      (_root_.Regex.Data.SparseSet.empty.insert ⟨3, by decide⟩ nfaEmpty_mem3) := by
  decide

private theorem nfaEmpty_mem1 :
    ¬ (⟨1, by decide⟩ : Fin nfaEmpty.nodes.size) ∈
      ((_root_.Regex.Data.SparseSet.empty.insert ⟨3, by decide⟩ nfaEmpty_mem3).insert
        ⟨2, by decide⟩ nfaEmpty_mem2) := by
  decide

private theorem nfaEmpty_mem0 :
    ¬ (⟨0, by decide⟩ : Fin nfaEmpty.nodes.size) ∈
      (((_root_.Regex.Data.SparseSet.empty.insert ⟨3, by decide⟩ nfaEmpty_mem3).insert
        ⟨2, by decide⟩ nfaEmpty_mem2).insert ⟨1, by decide⟩ nfaEmpty_mem1) := by
  decide

private theorem vm_any_empty_val (hay : String) (sz : Nat) :
    let nfa := _root_.Regex.NFA.compile (.group 0 .epsilon)
    (_root_.Regex.VM.captureNextBuf nfa _root_.Regex.NFA.compile_wf sz hay.startPos) =
      some ((_root_.Regex.Buffer.empty (s := hay) (size := sz)).setIfInBounds 0 (String.PosPlusOne.pos hay.startPos)
        |>.setIfInBounds 1 (String.PosPlusOne.pos hay.startPos)) := by
  have hnfa : _root_.Regex.NFA.compile (.group 0 .epsilon) = nfaEmpty := nfaEmpty_eq
  dsimp only
  simp only [hnfa]
  unfold _root_.Regex.VM.captureNextBuf
  rw [_root_.Regex.VM.captureNext.eq_def]
  have hstart : nfaEmpty.start = 3 := rfl
  let st3 : Fin nfaEmpty.nodes.size := ⟨nfaEmpty.start, (hnfa ▸ _root_.Regex.NFA.compile_wf).start_lt⟩
  have h3 : nfaEmpty[st3] = _root_.Regex.NFA.Node.save 0 2 := rfl
  have h2 : nfaEmpty[(⟨2, by decide⟩ : Fin nfaEmpty.nodes.size)] = _root_.Regex.NFA.Node.epsilon 1 := rfl
  have h1 : nfaEmpty[(⟨1, by decide⟩ : Fin nfaEmpty.nodes.size)] = _root_.Regex.NFA.Node.save 1 0 := rfl
  have h0 : nfaEmpty[(⟨0, by decide⟩ : Fin nfaEmpty.nodes.size)] = _root_.Regex.NFA.Node.done := rfl
  dsimp only
  rw [εClosure_save (σ := _root_.Regex.BufferStrategy hay sz) (nfa := nfaEmpty)
    (state := st3) (hmem := nfaEmpty_mem3) (off := 0) (next := 2) (hnode := h3)]
  simp only [st3, hstart]
  rw [εClosure_epsilon (next := 1) (hmem := nfaEmpty_mem2) (hnode := h2)]
  rw [εClosure_save (off := 1) (next := 0) (hmem := nfaEmpty_mem1) (hnode := h1)]
  rw [εClosure_done (hmem := nfaEmpty_mem0) (hnode := h0)]
  rw [_root_.Regex.VM.εClosure.eq_def]
  dsimp only
  exact captureNext_go_some_const (_root_.Regex.BufferStrategy hay sz)
    (hnfa ▸ _root_.Regex.NFA.compile_wf) hay.startPos _ _ _

private theorem empty_searchNext_any_isSome (hay : String) (hval : hay.startPosPlusOne.isValid = true) :
    ((_root_.Regex.fromExpr (.group 0 .epsilon)).searchNext (hay.startPosPlusOne.asPos hval)).isSome = true := by
  have hfc : _root_.Regex.Data.Expr.firstChars 8 (.group 0 .epsilon) = none := rfl
  have has : hay.startPosPlusOne.asPos hval = hay.startPos := rfl
  unfold _root_.Regex.searchNext _root_.Regex.fromExpr _root_.Regex.OptimizationInfo.fromExpr
    _root_.Regex.captureNextBuf _root_.Regex.OptimizationInfo.findStart
  dsimp only
  rw [hfc, Option.map_none]
  dsimp only
  rw [if_neg Bool.false_ne_true, has]
  have hbuf := vm_any_empty_val hay 2
  dsimp only at hbuf
  rw [hbuf]
  simp only [bind, Option.bind, pure, Vector.getElem_setIfInBounds]
  have hv : (String.PosPlusOne.pos hay.startPos).isValid = true := by simp
  have hle : String.PosPlusOne.pos hay.startPos ≤ String.PosPlusOne.pos hay.startPos :=
    Nat.le_refl _
  rw [dif_pos (by simp [hv, hle])]
  rfl

private theorem empty_matches_next_isSome :
    ((_root_.Regex.fromExpr (.group 0 .epsilon)).matches "").next?.isSome = true := by
  have hval : "".startPosPlusOne.isValid = true := by decide
  have hs := empty_searchNext_any_isSome "" hval
  unfold _root_.Regex.Matches.next? _root_.Regex.matches
  dsimp only
  rw [dif_pos hval]
  split
  · next h' => simp [h'] at hs
  · rfl

private theorem hval0_empty : "".startPosPlusOne.isValid = true := by decide
private theorem hvalNext_empty : ("".startPosPlusOne.next hval0_empty).isValid = false := by decide

private theorem empty_buf0_get0 :
    let re0 := _root_.Regex.fromExpr (.group 0 .epsilon)
    let buf0 : _root_.Regex.Buffer "" (re0.maxTag + 1) :=
      ((_root_.Regex.Buffer.empty (s := "") (size := re0.maxTag + 1)).setIfInBounds 0 (String.PosPlusOne.pos "".startPos)
        |>.setIfInBounds 1 (String.PosPlusOne.pos "".startPos))
    _root_.Regex.CapturedGroups.get ⟨buf0.toArray⟩ 0 =
      some ⟨"", "".startPos, "".startPos, by decide⟩ := by
  intro re0 buf0
  have hmax : re0.maxTag = 1 := by
    change (_root_.Regex.NFA.compile (.group 0 .epsilon)).maxTag = 1
    decide
  unfold _root_.Regex.CapturedGroups.get
  dsimp only [buf0]
  simp [hmax, _root_.Regex.Buffer.empty, String.PosPlusOne.pos]
  exact ⟨by decide, rfl⟩

private theorem empty_cap_next_eq :
    let re0 := _root_.Regex.fromExpr (.group 0 .epsilon)
    let buf0 : _root_.Regex.Buffer "" (re0.maxTag + 1) :=
      ((_root_.Regex.Buffer.empty (s := "") (size := re0.maxTag + 1)).setIfInBounds 0 (String.PosPlusOne.pos "".startPos)
        |>.setIfInBounds 1 (String.PosPlusOne.pos "".startPos))
    (_root_.Regex.Captures.mk re0 "".startPosPlusOne : _root_.Regex.Captures "").next? =
      some (⟨buf0.toArray⟩,
        { regex := re0, currentPos := "".startPosPlusOne.next hval0_empty }) := by
  intro re0 buf0
  have hfc : _root_.Regex.Data.Expr.firstChars 8 (.group 0 .epsilon) = none := rfl
  have has : "".startPosPlusOne.asPos hval0_empty = "".startPos := rfl
  have hcap : re0.captureNextBuf (re0.maxTag + 1) ("".startPosPlusOne.asPos hval0_empty) = some buf0 := by
    unfold _root_.Regex.captureNextBuf
    dsimp only [re0, _root_.Regex.fromExpr, _root_.Regex.OptimizationInfo.fromExpr,
      _root_.Regex.OptimizationInfo.findStart]
    rw [hfc, Option.map_none]
    dsimp only
    rw [if_neg Bool.false_ne_true, has]
    exact vm_any_empty_val "" (re0.maxTag + 1)
  have hget := empty_buf0_get0
  dsimp only at hget
  have hlt : ¬ ("".startPosPlusOne < String.PosPlusOne.pos "".startPos) := by decide
  unfold _root_.Regex.Captures.next?
  rw [dif_pos hval0_empty, hcap]
  dsimp only
  split
  · next h' => rw [hget] at h'; contradiction
  · next s h' =>
    rw [hget] at h'
    injection h' with hs
    subst hs
    simp [hlt, pure]

private theorem empty_replaceAll_empty_eq (rep : String) :
    (_root_.Regex.fromExpr (.group 0 .epsilon)).replaceAll "" rep = rep := by
  have hex1 : "".extract "".startPos "".startPos = "" := by decide
  have hex2 : "".extract "".startPos "".endPos = "" := by decide
  have hc1 := empty_cap_next_eq
  dsimp only at hc1
  have hget0 := empty_buf0_get0
  dsimp only at hget0
  have hc2 : (_root_.Regex.Captures.mk (_root_.Regex.fromExpr (.group 0 .epsilon))
      ("".startPosPlusOne.next hval0_empty) : _root_.Regex.Captures "").next? = none := by
    unfold _root_.Regex.Captures.next?
    rw [dif_neg (by simp [hvalNext_empty])]
    rfl
  unfold _root_.Regex.replaceAll _root_.Regex.transformAll _root_.Regex.captures
  rw [_root_.Regex.transformAll.go.eq_def]
  split
  · next g c' h1 =>
    rw [hc1] at h1
    injection h1 with hpair
    cases hpair
    dsimp only
    split
    · next s _ h2 =>
      rw [hget0] at h2
      injection h2 with hs
      subst hs
      rw [_root_.Regex.transformAll.go.eq_def]
      split
      · next _ _ h3 => simp [hc2] at h3
      · simp [hex1, hex2]
  · next h1 => simp [hc1] at h1

/-- Proof of `test_regex_emptyPattern_matchesAnyHaystack` for `liveApi`. -/
theorem proof_regex_emptyPattern_matchesAnyHaystack :
    AllPass (test_regex_emptyPattern_matchesAnyHaystack liveApi) := by
  intro hay
  simp only [liveApi, compilePattern, parse_empty_ok, bind, Except.bind, pure, Except.pure,
    _root_.Regex.test, assert]
  have hval : hay.startPosPlusOne.isValid = true := by simp [String.startPosPlusOne]
  have hs := empty_searchNext_any_isSome hay hval
  unfold _root_.Regex.find _root_.Regex.Matches.next? _root_.Regex.matches
  dsimp only
  rw [dif_pos hval]
  split
  · next h' => simp [h'] at hs
  · exact ⟨rfl, trivial⟩

/-- Proof of `test_regex_replaceAll_emptyOnEmpty_eqReplacement` for `liveApi`. -/
theorem proof_regex_replaceAll_emptyOnEmpty_eqReplacement :
    AllPass (test_regex_replaceAll_emptyOnEmpty_eqReplacement liveApi) := by
  intro rep
  simp only [liveApi, compilePattern, parse_empty_ok, bind, Except.bind, pure, Except.pure, assert]
  exact ⟨empty_replaceAll_empty_eq rep, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_regex_onError_returnsNonEmptyMessage` on `liveApi`. -/
theorem reach_regex_onError_returnsNonEmptyMessage :
    CanReach (test_regex_onError_returnsNonEmptyMessage liveApi) := by
  refine ⟨"[", "hello", ?_⟩
  simp only [liveApi, compilePattern, parse_lbracket_err, mapError, assert]
  exact ⟨error_toString_ne_empty _, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_regex_testPattern_iff_findFirstSome` on `liveApi`. -/
theorem reach_regex_testPattern_iff_findFirstSome :
    CanReach (test_regex_testPattern_iff_findFirstSome liveApi) := by
  refine ⟨"", "", ?_⟩
  have h := proof_regex_testPattern_iff_findFirstSome "" ""
  simp only [liveApi, compilePattern, parse_empty_ok, bind, Except.bind, pure, Except.pure,
    assert] at h ⊢
  exact h

/-- Non-vacuity `CanReach` witness for `test_regex_countMatches_eq_findAllSize` on `liveApi`. -/
theorem reach_regex_countMatches_eq_findAllSize :
    CanReach (test_regex_countMatches_eq_findAllSize liveApi) := by
  refine ⟨"", "", ?_⟩
  have h := proof_regex_countMatches_eq_findAllSize "" ""
  simp only [liveApi, compilePattern, parse_empty_ok, bind, Except.bind, pure, Except.pure,
    assert] at h ⊢
  exact h

/-- Non-vacuity `CanReach` witness for `test_regex_findAll_spansValid` on `liveApi`. -/
theorem reach_regex_findAll_spansValid :
    CanReach (test_regex_findAll_spansValid liveApi) := by
  refine ⟨"", "", ?_⟩
  have hn := empty_matches_next_isSome
  cases hnx : ((_root_.Regex.fromExpr (.group 0 .epsilon)).matches "").next? with
  | none => simp [hnx] at hn
  | some p =>
    have hge : 1 ≤ ((_root_.Regex.fromExpr (.group 0 .epsilon)).findAll "").size := by
      unfold _root_.Regex.findAll
      rw [_root_.Regex.findAll.go, hnx]
      exact findAll_go_size_mono p.2 #[p.1]
    have hlt : 0 < ((_root_.Regex.fromExpr (.group 0 .epsilon)).findAll "").size := hge
    have hall := proof_regex_findAll_spansValid "" ""
    simp only [liveApi, compilePattern, parse_empty_ok, bind, Except.bind, pure, Except.pure,
      Array.size_map, assert] at hall ⊢
    exact ⟨0, hlt, (hall 0 hlt).1, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_regex_splitBy_nonEmpty` on `liveApi`. -/
theorem reach_regex_splitBy_nonEmpty :
    CanReach (test_regex_splitBy_nonEmpty liveApi) := by
  refine ⟨"", "", ?_⟩
  have h := proof_regex_splitBy_nonEmpty "" ""
  simp only [liveApi, compilePattern, parse_empty_ok, bind, Except.bind, pure, Except.pure,
    assert] at h ⊢
  exact h

/-- Non-vacuity `CanReach` witness for `test_regex_emptyPattern_matchesAnyHaystack` on `liveApi`. -/
theorem reach_regex_emptyPattern_matchesAnyHaystack :
    CanReach (test_regex_emptyPattern_matchesAnyHaystack liveApi) := by
  refine ⟨"abc", ?_⟩
  have h := proof_regex_emptyPattern_matchesAnyHaystack "abc"
  simp only [liveApi, compilePattern, parse_empty_ok, bind, Except.bind, pure, Except.pure,
    assert] at h ⊢
  exact h

/-- Non-vacuity `CanReach` witness for `test_regex_replaceAll_emptyOnEmpty_eqReplacement` on `liveApi`. -/
theorem reach_regex_replaceAll_emptyOnEmpty_eqReplacement :
    CanReach (test_regex_replaceAll_emptyOnEmpty_eqReplacement liveApi) := by
  refine ⟨"X", ?_⟩
  have h := proof_regex_replaceAll_emptyOnEmpty_eqReplacement "X"
  simp only [liveApi, compilePattern, parse_empty_ok, bind, Except.bind, pure, Except.pure,
    assert] at h ⊢
  exact h

end Packages.Regex.Proofs

import LeanSwe.CmdLine.Interface
import LeanSwe.CmdLine.SpecTests
import LeanSwe.CmdLine.Proofs.ParserCore
namespace LeanSwe.CmdLine.Proofs
open Core Core.NondetTest LeanSwe.CmdLine LeanSwe.CmdLine.Proofs.Shared
private theorem resolveSingleOption_pureNoEnv (opt : OptSpec) (cliVals : List OptValue) :
    Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt cliVals [] =
      if !cliVals.isEmpty then
        if !opt.repeatable && decide (cliVals.length > 1) then
          .error { kind := .invalidValue, message := s!"option '{opt.name}' cannot be specified multiple times", target := some opt.name }
        else .ok (some cliVals)
      else Model.resolveOptDefault opt [] := by
  unfold Model.resolveSingleOption; by_cases hne : !cliVals.isEmpty
  · simp [hne, pure]
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]; cases opt.envVar <;> simp [pure, Bind.bind, Internal.pureNoEnvOps]
private theorem resolveOptDefault_ok_props (opt : OptSpec) {r : Option (List OptValue)} (h : Model.resolveOptDefault opt [] = .ok r) :
    match r with | none => True | some vals => vals ≠ [] ∧ vals.length = 1 ∧ ∀ v ∈ vals, OptValueMatchesKind opt.kind v := by
  unfold Model.resolveOptDefault at h; cases hd : opt.default with
  | some d =>
    rw [hd] at h; dsimp only at h; rw [parseOptValueWith_nil] at h; cases hp : Model.parseOptValue opt.kind d with
    | error _ => rw [hp] at h; cases h
    | ok v => rw [hp] at h; injection h with hr; subst hr; exact ⟨by simp, by simp, fun v' hv' => by simp at hv'; subst hv'; exact parseOptValue_ok_matchesKind hp⟩
  | none =>
    rw [hd] at h; dsimp only at h; by_cases hreq : opt.required; · simp [hreq] at h
    · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at h; by_cases hbool : (opt.kind == .bool && !opt.repeatable)
      · simp only [hbool, ↓reduceIte, Except.ok.injEq] at h; subst h; have hk := valueKind_eq_of_beq ((Bool.and_eq_true _ _).mp hbool).1; exact ⟨by simp, by simp, fun v' hv' => by simp at hv'; subst hv'; rw [hk]; trivial⟩
      · simp only [hbool, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h; subst h; trivial
private theorem resolveOptions_cons (opt : OptSpec) (rest : List OptSpec) (cliOpts : List (String × List OptValue)) :
    Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv (opt :: rest) cliOpts [] =
      (match Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt (lookupCli cliOpts opt.name) [] with
       | .error e => .error e
       | .ok resolved? => match Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv rest cliOpts [] with
         | .error e => .error e | .ok tail => match resolved? with | none => .ok tail | some vals => .ok ((opt.name, vals) :: tail)) := by cases rest <;> rfl
private theorem resolveOptions_mem_keys (visibleOpts : List OptSpec) (cliOpts resolved : List (String × List OptValue))
    (h : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv visibleOpts cliOpts [] = .ok resolved) : ∀ p ∈ resolved, ∃ opt ∈ visibleOpts, opt.name = p.1 := by
  induction visibleOpts generalizing resolved with
  | nil => change Except.ok [] = Except.ok resolved at h; injection h with heq; subst heq; intro p hp; cases hp
  | cons opt rest ih =>
    rw [resolveOptions_cons] at h; cases hs : Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt (lookupCli cliOpts opt.name) [] with
    | error _ => rw [hs] at h; cases h
    | ok res? =>
      rw [hs] at h; cases ht : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv rest cliOpts [] with
      | error _ => rw [ht] at h; cases h
      | ok tail =>
        rw [ht] at h; cases res? with
        | none => rw [Except.ok.injEq] at h; subst h; intro p hp; rcases ih tail ht p hp with ⟨o, ho, heq⟩; exact ⟨o, by simp [ho], heq⟩
        | some _ =>
          rw [Except.ok.injEq] at h; subst h; intro p hp; rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨opt, by simp, rfl⟩
          · rcases ih tail ht p hp with ⟨o, ho, heq⟩; exact ⟨o, by simp [ho], heq⟩
private theorem resolveOptions_lookup_not_mem (visibleOpts : List OptSpec) (cliOpts resolved : List (String × List OptValue)) (k : String)
    (h : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv visibleOpts cliOpts [] = .ok resolved) (hnot : ∀ opt ∈ visibleOpts, opt.name ≠ k) : lookupCli resolved k = [] := by
  have hmem := resolveOptions_mem_keys visibleOpts cliOpts resolved h; clear h
  induction resolved with
  | nil => rfl
  | cons p _ ih =>
    rcases p with ⟨k', vs⟩; by_cases hkk : k' == k
    · rcases hmem (k', vs) (by simp) with ⟨o, ho, hon⟩; exact absurd hon (by have := beq_iff_eq.mp hkk; subst this; exact hnot o ho)
    · simp only [lookupCli, List.find?, Bool.eq_false_iff.mpr hkk]; exact ih (fun q hq => hmem q (by simp [hq]))
private theorem list_optValue_beq_single_false {xs : List OptValue} (h : (xs == [.bool false]) = true) : xs = [.bool false] := by
  cases xs with
  | nil => cases h
  | cons x xs => cases xs with | cons _ _ => cases (x == .bool false) <;> simp [BEq.beq, List.beq] at h | nil => simp only [BEq.beq, List.beq] at h; cases x <;> first | (rename_i b; cases b <;> first | rfl | cases h) | cases h
private theorem resolveOptions_lookup_aux (opts : List OptSpec) (cliOpts resolved : List (String × List OptValue)) (hnd : (opts.map (·.name)).Nodup)
    (hcli : ∀ opt ∈ opts, ∀ v ∈ lookupCli cliOpts opt.name, OptValueMatchesKind opt.kind v ∧ (opt.kind == .bool && opt.repeatable → v = .bool true) ∧ (opt.kind == .bool && opt.long.isNone → v = .bool true))
    (h : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv opts cliOpts [] = .ok resolved) :
    ∀ opt ∈ opts, let vals := lookupCli resolved opt.name
      (∀ v ∈ vals, OptValueMatchesKind opt.kind v) ∧ (opt.repeatable = false → vals.length ≤ 1) ∧ (vals = [] → lookupCli cliOpts opt.name = []) ∧
      ((opt.kind == .bool && !opt.repeatable && opt.long.isNone && (vals == [.bool false])) = true → lookupCli cliOpts opt.name = []) ∧
      (vals ≠ [] → Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt (lookupCli cliOpts opt.name) [] = .ok (some vals)) := by
  induction opts generalizing resolved with
  | nil => intro opt ho; cases ho
  | cons o rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hnotRest : ∀ o' ∈ rest, o'.name ≠ o.name := fun o' ho' heq => hnd.1 ⟨o', ho', heq⟩
    rw [resolveOptions_cons] at h
    cases hs : Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv o (lookupCli cliOpts o.name) [] with
    | error _ => rw [hs] at h; cases h
    | ok res? =>
      rw [hs] at h
      cases ht : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv rest cliOpts [] with
      | error _ => rw [ht] at h; cases h
      | ok tail =>
        rw [ht] at h; have hih := ih tail hnd.2 (fun o' ho' => hcli o' (by simp [ho'])) ht; have hs' := hs; rw [resolveSingleOption_pureNoEnv] at hs'
        intro opt ho; rcases List.mem_cons.mp ho with rfl | hmem
        · have hc := hcli opt (by simp)
          by_cases hne : !(lookupCli cliOpts opt.name).isEmpty
          · simp only [hne, ↓reduceIte] at hs'
            by_cases hlen : (!opt.repeatable && decide ((lookupCli cliOpts opt.name).length > 1))
            · simp [hlen] at hs'
            · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hs'; injection hs' with hrs; subst hrs; rw [Except.ok.injEq] at h; subst h; rw [show lookupCli ((opt.name, lookupCli cliOpts opt.name) :: tail) opt.name = lookupCli cliOpts opt.name from by simp [lookupCli, List.find?]]
              refine ⟨fun v hv => (hc v hv).1, (fun hnr => by simp only [hnr, Bool.not_false, Bool.true_and, decide_eq_true_eq, Nat.not_lt] at hlen; exact hlen), (fun hnil => by rw [hnil] at hne; cases hne), ?_, fun _ => hs⟩
              intro hcond; simp only [Bool.and_eq_true] at hcond; rcases hcond with ⟨⟨⟨hkb, _⟩, hln⟩, heqv⟩; cases ((hc (.bool false) (by rw [list_optValue_beq_single_false heqv]; simp)).2.2 (by simp [hkb, hln]))
          · simp only [Bool.eq_false_iff.mpr hne, Bool.false_eq_true, ↓reduceIte] at hs'; have hcliNil : lookupCli cliOpts opt.name = [] := by cases hcl : lookupCli cliOpts opt.name <;> first | rfl | (simp [hcl] at hne)
            have hdef := resolveOptDefault_ok_props opt hs'; cases res? with
            | none => rw [Except.ok.injEq] at h; subst h; rw [resolveOptions_lookup_not_mem rest cliOpts tail opt.name ht hnotRest]; exact ⟨(fun _ h => by cases h), (fun _ => by simp), (fun _ => hcliNil), (fun _ => hcliNil), (fun hne' => absurd rfl hne')⟩
            | some vs => rw [Except.ok.injEq] at h; subst h; rw [show lookupCli ((opt.name, vs) :: tail) opt.name = vs from by simp [lookupCli, List.find?]]; rcases hdef with ⟨hvne, hvlen, hvkind⟩; exact ⟨hvkind, fun _ => Nat.le_of_eq hvlen, fun hnil => absurd hnil hvne, fun _ => hcliNil, fun _ => hs⟩
        · have htail : lookupCli resolved opt.name = lookupCli tail opt.name := by cases res? with | none => rw [Except.ok.injEq] at h; subst h; rfl | some _ => rw [Except.ok.injEq] at h; subst h; unfold lookupCli; simp [beq_false_of_ne (hnotRest opt hmem).symm]
          rw [htail]; exact hih opt hmem
private theorem resolveOptions_congr (opts : List OptSpec) (cli1 cli2 : List (String × List OptValue))
    (h : ∀ opt ∈ opts, Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt (lookupCli cli1 opt.name) [] = Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt (lookupCli cli2 opt.name) []) :
    Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv opts cli1 [] = Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv opts cli2 [] := by
  induction opts with | nil => rfl | cons o _ ih => rw [resolveOptions_cons, resolveOptions_cons, h o (by simp), ih (fun o' ho' => h o' (by simp [ho']))]
private theorem parseTokensLoop_subPath_aux (rootName : String) (path : List String) (globals : List OptSpec) (effVer : Option String) (targetSpec : CommandSpec) :
    ∀ g0 v0 cur sp, NodeInv cur g0 v0 → Model.findSubcommandPath.go g0 v0 cur path = .ok (globals, effVer, targetSpec) →
      Internal.parseTokensLoop rootName [] { curSpec := cur, subPath := sp, inheritedGlobals := g0, effectiveVersion := cur.version <|> v0 } path =
        .ok { curSpec := targetSpec, subPath := sp ++ path, inheritedGlobals := globals, effectiveVersion := effVer } := by
  induction path with
  | nil => intro g0 v0 cur sp _ hgo; unfold Model.findSubcommandPath.go at hgo; injection hgo with hp; injection hp with hg ht; injection ht with hv hc; subst hg hv hc; simp [Internal.parseTokensLoop]
  | cons p _ ih =>
    intro g0 v0 cur sp hnode hgo; unfold Model.findSubcommandPath.go at hgo; cases hfs : cur.subcommands.find? (fun s => s.name == p) with
    | none => simp [hfs] at hgo
    | some next =>
      simp only [hfs] at hgo; have hmem := List.mem_of_find?_eq_some hfs; have hsubNode := nodeInv_sub hnode hmem; have hsubProps := nodeInv_props hsubNode
      have hnameEq : next.name = p := beq_iff_eq.mp (List.find?_some (p := fun (s : CommandSpec) => s.name == p) hfs)
      have ⟨hne, hnodash⟩ := isValidCommandName_props hsubProps.validName; rw [hnameEq] at hne hnodash
      have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList p (fun heq => hnodash ['-'] (by rw [heq])) (fun heq => hnodash ['-', 'h', 'e', 'l', 'p'] (by rw [heq])) (fun heq => hnodash ['-', 'v', 'e', 'r', 's', 'i', 'o', 'n'] (by rw [heq]))
      have hnotEmpty : cur.subcommands.isEmpty = false := by cases hc : cur.subcommands with | nil => rw [hc] at hmem; cases hmem | cons _ _ => rfl
      unfold Internal.parseTokensLoop Internal.stepToken; simp only [beq_false_of_ne hne_dd, beq_false_of_ne hne_help, beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      cases htl : p.toList with
      | nil => exact absurd htl hne
      | cons c1 _ =>
        have hc1n : c1 ≠ '-' := fun heq => by subst heq; exact hnodash _ htl
        split
        · rename_i _ heqm; exact absurd (List.cons.inj heqm).1 hc1n
        · rename_i _ _ _ heqm; exact absurd (List.cons.inj heqm).1 hc1n
        · simp only [hnotEmpty, Bool.not_false, List.isEmpty_nil, Bool.and_self, ↓reduceIte, hfs, hnameEq, Bind.bind, Except.bind]; simpa [List.append_assoc] using ih (g0 ++ cur.options) (cur.version <|> v0) next (sp ++ [p]) hsubNode hgo
private theorem parseTokensLoop_subPath (rootSpec : CommandSpec) (path : List String) {globals : List OptSpec} {effVer : Option String} {targetSpec : CommandSpec}
    (hvalid : Model.isValidSpec rootSpec = true) (hpath : Model.findSubcommandPath rootSpec path = .ok (globals, effVer, targetSpec)) :
    Internal.parseTokensLoop rootSpec.name [] { curSpec := rootSpec, effectiveVersion := rootSpec.version } path =
      .ok { curSpec := targetSpec, subPath := path, inheritedGlobals := globals, effectiveVersion := effVer } := by
  have hnodeRoot : NodeInv rootSpec [] none := ⟨by simpa [Model.isValidSpec] using hvalid, rfl⟩
  have hver : rootSpec.version = (rootSpec.version <|> none) := by cases rootSpec.version <;> rfl
  rw [hver]; exact parseTokensLoop_subPath_aux rootSpec.name path globals effVer targetSpec [] none rootSpec [] hnodeRoot hpath
private theorem stepToken_longBool (rootName : String) (st : Internal.ParseState) (opt : OptSpec) (l : String) (b : Bool)
    (hndLongs : (Model.collectVisibleLongs (st.inheritedGlobals ++ st.curSpec.options)).Nodup) (hloc : Model.isValidOptLocal opt = true)
    (ho : opt ∈ st.inheritedGlobals ++ st.curSpec.options) (hl : opt.long = some l) (hk : opt.kind = .bool) (hnr : b = false → opt.repeatable = false)
    (hp : st.pendingOpt = none) (had : st.afterDashDash = false) :
    Internal.stepToken rootName [] st (if b then "--" ++ l else "--no-" ++ l) = .ok { st with cliOpts := Internal.recordCliOpt st.cliOpts opt.name (.bool b) } := by
  have ⟨hlne, hlhelp, hlver, hleq, _, _⟩ := isValidOptLocal_long_props hloc hl
  cases b with
  | true =>
    have hlist : ("--" ++ l).toList = '-' :: '-' :: l.toList := by rw [String.toList_append]; rfl
    have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList ("--" ++ l)
      (fun heq => by rw [hlist] at heq; exact hlne (List.cons.inj (List.cons.inj heq).2).2)
      (fun heq => by rw [hlist] at heq; exact hlhelp (by have h := congrArg String.ofList (List.cons.inj (List.cons.inj heq).2).2; simpa [String.ofList_toList] using h))
      (fun heq => by rw [hlist] at heq; exact hlver (by have h := congrArg String.ofList (List.cons.inj (List.cons.inj heq).2).2; simpa [String.ofList_toList] using h))
    have hlkp := lookupLongOpt_pos (st.inheritedGlobals ++ st.curSpec.options) hndLongs ho hl
    have hsf : Internal.splitFirstEq (String.ofList l.toList) = (l, none) := by rw [String.ofList_toList]; exact splitFirstEq_none l hleq
    have hnie : l.isEmpty = false := by cases h : l.toList <;> simp_all [String.isEmpty]
    have hnhv : ((l == "help") || (l == "version" && st.effectiveVersion.isSome)) = false := by simp [beq_false_of_ne hlhelp, beq_false_of_ne hlver]
    unfold Internal.stepToken; simp only [hp, had, beq_false_of_ne hne_dd, beq_false_of_ne hne_help, beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i longRest heq; rw [hlist] at heq; have hlr := (List.cons.inj (List.cons.inj heq).2).2; rw [← hlr, hsf]; have hvb : (ValueKind.bool == ValueKind.bool) = true := rfl; simp [hnie, hnhv, hlkp, hk, hvb]
    · rename_i _ _ h1 heq; rw [hlist] at heq; injection heq with _ h2; injection h2 with hc _; subst hc; exact False.elim (h1 rfl)
    · rename_i _ h1 _; exact False.elim (h1 _ hlist)
  | false =>
    have hnr' := hnr rfl; have hlist : ("--no-" ++ l).toList = '-' :: '-' :: ('n' :: 'o' :: '-' :: l.toList) := by rw [String.toList_append]; rfl
    have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList ("--no-" ++ l) (fun heq => by rw [hlist] at heq; cases heq) (fun heq => by rw [hlist] at heq; cases heq) (fun heq => by rw [hlist] at heq; cases heq)
    have hlkp := lookupLongOpt_neg (st.inheritedGlobals ++ st.curSpec.options) hndLongs ho hk hnr' hl
    have hno_eq : '=' ∉ ("no-" ++ l).toList := by rw [String.toList_append]; have hpre : ("no-").toList = ['n', 'o', '-'] := rfl; rw [hpre]; simp [hleq]
    have hsf : Internal.splitFirstEq (String.ofList ('n' :: 'o' :: '-' :: l.toList)) = ("no-" ++ l, none) := by
      have h1 : ('n' :: 'o' :: '-' :: l.toList) = ("no-" ++ l).toList := by rw [String.toList_append]; rfl
      rw [h1, String.ofList_toList]; exact splitFirstEq_none ("no-" ++ l) hno_eq
    have hnie : ("no-" ++ l).isEmpty = false := by simp [String.isEmpty]
    have hnhv : (("no-" ++ l == "help") || ("no-" ++ l == "version" && st.effectiveVersion.isSome)) = false := by
      have hn1 : "no-" ++ l ≠ "help" := fun heq => by have := congrArg String.toList heq; simp [String.toList_append] at this
      have hn2 : "no-" ++ l ≠ "version" := fun heq => by have := congrArg String.toList heq; simp [String.toList_append] at this
      simp [beq_false_of_ne hn1, beq_false_of_ne hn2]
    unfold Internal.stepToken; simp only [hp, had, beq_false_of_ne hne_dd, beq_false_of_ne hne_help, beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i longRest heq; rw [hlist] at heq; have hlr := (List.cons.inj (List.cons.inj heq).2).2; rw [← hlr, hsf]; simp [hnie, hnhv, hlkp]
    · rename_i _ _ h1 heq; rw [hlist] at heq; injection heq with _ h2; injection h2 with hc _; subst hc; exact False.elim (h1 rfl)
    · rename_i _ h1 _; exact False.elim (h1 _ hlist)
private theorem stepToken_longVal (rootName : String) (st : Internal.ParseState) (opt : OptSpec) (l : String) (v : OptValue)
    (hndLongs : (Model.collectVisibleLongs (st.inheritedGlobals ++ st.curSpec.options)).Nodup) (hloc : Model.isValidOptLocal opt = true)
    (ho : opt ∈ st.inheritedGlobals ++ st.curSpec.options) (hl : opt.long = some l) (hnbool : opt.kind ≠ .bool) (hmatch : OptValueMatchesKind opt.kind v)
    (hp : st.pendingOpt = none) (had : st.afterDashDash = false) :
    Internal.stepToken rootName [] st ("--" ++ l ++ "=" ++ Model.optValueToString v) = .ok { st with cliOpts := Internal.recordCliOpt st.cliOpts opt.name v } := by
  have ⟨hlne, hlhelp, hlver, hleq, _, _⟩ := isValidOptLocal_long_props hloc hl
  have hlist : ("--" ++ l ++ "=" ++ Model.optValueToString v).toList = '-' :: '-' :: (l.toList ++ ('=' :: (Model.optValueToString v).toList)) := by
    rw [String.toList_append, String.toList_append, String.toList_append, show ("--").toList = ['-', '-'] from rfl, show ("=").toList = ['='] from rfl]; simp [List.append_assoc]
  have hmem : '=' ∈ ("--" ++ l ++ "=" ++ Model.optValueToString v).toList := by rw [hlist]; simp
  have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList ("--" ++ l ++ "=" ++ Model.optValueToString v) (fun heq => by have := hmem; rw [heq] at this; simp at this) (fun heq => by have := hmem; rw [heq] at this; simp at this) (fun heq => by have := hmem; rw [heq] at this; simp at this)
  have hlkp := lookupLongOpt_pos (st.inheritedGlobals ++ st.curSpec.options) hndLongs ho hl
  have hsf : Internal.splitFirstEq (String.ofList (l.toList ++ ('=' :: (Model.optValueToString v).toList))) = (l, some (Model.optValueToString v)) := by
    have heql : String.ofList (l.toList ++ ('=' :: (Model.optValueToString v).toList)) = l ++ "=" ++ Model.optValueToString v := by
      have h1 : (l ++ "=" ++ Model.optValueToString v).toList = l.toList ++ ('=' :: (Model.optValueToString v).toList) := by simp [String.toList_append]
      rw [← h1, String.ofList_toList]
    rw [heql]; exact splitFirstEq_append l (Model.optValueToString v) hleq
  have hnie : l.isEmpty = false := by simp [String.isEmpty]; exact fun hc => by subst hc; exact hlne rfl
  have hnhv : ((l == "help") || (l == "version" && st.effectiveVersion.isSome)) = false := by simp [beq_false_of_ne hlhelp, beq_false_of_ne hlver]
  have hnb : (opt.kind == .bool) = false := valueKind_beq_false_of_ne hnbool; have hpv := parseOptValue_optValueToString hmatch
  unfold Internal.stepToken; simp only [hp, had, beq_false_of_ne hne_dd, beq_false_of_ne hne_help, beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i longRest heq; rw [hlist] at heq; have hlr := (List.cons.inj (List.cons.inj heq).2).2; rw [← hlr, hsf]; simp [hnie, hnhv, hlkp, hnb, Shared.parseOptValueWithFast_eq, parseOptValueWith_nil, hpv, Bind.bind, Except.bind]
  · rename_i _ _ h1 heq; rw [hlist] at heq; injection heq with _ h2; injection h2 with hc _; subst hc; exact False.elim (h1 rfl)
  · rename_i _ h1 _; exact False.elim (h1 _ hlist)
private theorem stepToken_short_aux {ver : Option String} (rootName : String) (st : Internal.ParseState) (opt : OptSpec) (c : Char)
    (heff : st.effectiveVersion = (st.curSpec.version <|> ver)) (hprops : NodeProps st.curSpec st.inheritedGlobals ver) (ho : opt ∈ st.inheritedGlobals ++ st.curSpec.options)
    (hs : opt.short = some c) (hp : st.pendingOpt = none) (had : st.afterDashDash = false) :
    Internal.stepToken rootName [] st ("-" ++ String.singleton c) =
      if opt.kind == .bool then .ok { st with cliOpts := Internal.recordCliOpt st.cliOpts opt.name (.bool true) } else .ok { st with pendingOpt := some opt } := by
  have hc_ne := isValidOptLocal_short_ne_dash (hprops.validOpts opt ho) hs
  have hlist : ("-" ++ String.singleton c).toList = ['-', c] := by rw [String.toList_append, String.toList_singleton]; rfl
  have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList ("-" ++ String.singleton c)
    (fun heq => by rw [hlist] at heq; exact hc_ne (List.cons.inj (List.cons.inj heq).2).1)
    (fun heq => by rw [hlist] at heq; exact hc_ne (List.cons.inj (List.cons.inj heq).2).1)
    (fun heq => by rw [hlist] at heq; exact hc_ne (List.cons.inj (List.cons.inj heq).2).1)
  have hcmem : c ∈ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short) := List.mem_filterMap.mpr ⟨opt, ho, hs⟩
  have hnh : (c == 'h' && st.curSpec.shortHelp) = false := by
    cases hsh : st.curSpec.shortHelp
    · simp
    · by_cases hch : c = 'h'
      · subst hch; exact absurd hcmem (hprops.noShortHelp hsh)
      · simp [beq_false_of_ne hch]
  have hnV : (c == 'V' && st.curSpec.shortVersion && st.effectiveVersion.isSome) = false := by
    rw [heff]; cases hsv : (st.curSpec.shortVersion && (st.curSpec.version <|> ver).isSome)
    · cases h1 : st.curSpec.shortVersion <;> cases h2 : (st.curSpec.version <|> ver).isSome <;> simp_all
    · by_cases hcV : c = 'V' <;> first | (subst hcV; exact absurd hcmem (hprops.noShortVer hsv)) | simp [beq_false_of_ne hcV]
  have hfind := find?_unique_key (·.short) (st.inheritedGlobals ++ st.curSpec.options) hprops.nodupShorts opt ho c hs
  unfold Internal.stepToken; simp only [hp, had, beq_false_of_ne hne_dd, beq_false_of_ne hne_help, beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rw [hlist]
  split
  · rename_i _ heq; exact absurd (List.cons.inj (List.cons.inj heq).2).1 hc_ne
  · rename_i _ c' sr' _ heq
    rw [← (List.cons.inj (List.cons.inj heq).2).1, ← (List.cons.inj (List.cons.inj heq).2).2]; unfold Internal.parseShortBundle; simp only [hnh, hnV, hfind, Bool.false_eq_true, ↓reduceIte]
    by_cases hbool : opt.kind == .bool
    · simp only [hbool, ↓reduceIte]; unfold Internal.parseShortBundle; simp [Bind.bind, Except.bind]
    · have hbf := Bool.eq_false_iff.mpr hbool; simp only [hbf, Bool.false_eq_true, ↓reduceIte]; rfl
  · rename_i _ _ h2; exact absurd rfl (h2 c [])
private theorem renderValueList_cons (opt : OptSpec) (v : OptValue) (vs : List OptValue) :
    Model.renderSingleOpt.renderValueList opt (v :: vs) =
      (if opt.kind == .bool && v != .bool true then .error { kind := .invalidValue, message := s!"repeatable boolean option '{opt.name}' cannot render false value", target := some opt.name }
       else do
         let toks ← match opt.long with | some l => if opt.kind == .bool then .ok ["--" ++ l] else .ok ["--" ++ l ++ "=" ++ Model.optValueToString v] | none => match opt.short with | some c => if opt.kind == .bool then .ok ["-" ++ String.singleton c] else .ok ["-" ++ String.singleton c, Model.optValueToString v] | none => .error { kind := .invalidSpec, message := s!"option '{opt.name}' has neither long nor short flag" }
         let rest ← Model.renderSingleOpt.renderValueList opt vs
         .ok (toks ++ rest)) := by cases vs <;> rfl
private theorem parseTokensLoop_renderValueList {ver : Option String} (rootName : String) (st : Internal.ParseState) (opt : OptSpec) (vals : List OptValue) (toks : List String)
    (heff : st.effectiveVersion = (st.curSpec.version <|> ver)) (hprops : NodeProps st.curSpec st.inheritedGlobals ver) (ho : opt ∈ st.inheritedGlobals ++ st.curSpec.options)
    (hmatch : ∀ v ∈ vals, OptValueMatchesKind opt.kind v) (hp : st.pendingOpt = none) (had : st.afterDashDash = false) (hr : Model.renderSingleOpt.renderValueList opt vals = .ok toks) :
    Internal.parseTokensLoop rootName [] st toks = .ok { st with cliOpts := recordCliOptMany st.cliOpts opt.name vals } := by
  have hloc := hprops.validOpts opt ho; induction vals generalizing st toks with
  | nil => have hnil : Model.renderSingleOpt.renderValueList opt [] = .ok [] := rfl; rw [hnil] at hr; injection hr with heq; subst heq; cases st; simp only at hp; subst hp; rfl
  | cons v vs ih =>
    rw [renderValueList_cons] at hr; by_cases hbf : (opt.kind == .bool && v != .bool true); · simp [hbf] at hr
    · simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hr; have hv_match := hmatch v (by simp); have hvs_match : ∀ v' ∈ vs, OptValueMatchesKind opt.kind v' := fun v' hv' => hmatch v' (by simp [hv'])
      have hstep1 : Internal.parseTokensLoop rootName [] st (match opt.long with | some l => if opt.kind == .bool then ["--" ++ l] else ["--" ++ l ++ "=" ++ Model.optValueToString v] | none => match opt.short with | some c => if opt.kind == .bool then ["-" ++ String.singleton c] else ["-" ++ String.singleton c, Model.optValueToString v] | none => []) = .ok { st with cliOpts := Internal.recordCliOpt st.cliOpts opt.name v } := by
        cases hl : opt.long with
        | some l =>
          by_cases hbool : opt.kind == .bool
          · simp only [hbool, ↓reduceIte]; have hk := valueKind_eq_of_beq hbool; have hv : v = .bool true := by cases hv' : v <;> rw [hk, hv'] at hv_match <;> simp [OptValueMatchesKind] at hv_match; rename_i b; cases b <;> first | rfl | (exfalso; apply hbf; simp [hk, hv']; decide)
            subst hv; have h1 := stepToken_longBool rootName st opt l true hprops.nodupLongs hloc ho hl hk (fun hc => by cases hc) hp had; simp only [↓reduceIte] at h1; unfold Internal.parseTokensLoop; rw [h1]; rfl
          · simp only [hbool, Bool.false_eq_true, ↓reduceIte]; have h1 := stepToken_longVal rootName st opt l v hprops.nodupLongs hloc ho hl (fun hk => hbool (by simp [hk]; rfl)) hv_match hp had; unfold Internal.parseTokensLoop; rw [h1]; rfl
        | none =>
          cases hs : opt.short with | none => rw [hl, hs] at hr; simp [Bind.bind, Except.bind] at hr | some c =>
            by_cases hbool : opt.kind == .bool
            · simp only [hbool, ↓reduceIte]; have hk := valueKind_eq_of_beq hbool; have hv : v = .bool true := by cases hv' : v <;> rw [hk, hv'] at hv_match <;> simp [OptValueMatchesKind] at hv_match; rename_i b; cases b <;> first | rfl | (exfalso; apply hbf; simp [hk, hv']; decide)
              subst hv; have h1 := stepToken_short_aux rootName st opt c heff hprops ho hs hp had; simp only [hbool, ↓reduceIte] at h1; unfold Internal.parseTokensLoop; rw [h1]; rfl
            · simp only [hbool, Bool.false_eq_true, ↓reduceIte]; have h1 := stepToken_short_aux rootName st opt c heff hprops ho hs hp had; simp only [hbool, Bool.false_eq_true, ↓reduceIte] at h1; have hpv := parseOptValue_optValueToString hv_match
              have h2 : Internal.stepToken rootName [] { st with pendingOpt := some opt } (Model.optValueToString v) = .ok { st with cliOpts := Internal.recordCliOpt st.cliOpts opt.name v } := by unfold Internal.stepToken; simp [Shared.parseOptValueWithFast_eq, parseOptValueWith_nil, hpv, hp, Bind.bind, Except.bind]
              unfold Internal.parseTokensLoop; rw [h1]; dsimp only [Bind.bind, Except.bind]; unfold Internal.parseTokensLoop; rw [h2]; rfl
      cases hl : opt.long <;> rw [hl] at hr hstep1 <;> dsimp only at hr hstep1
      · cases hs : opt.short <;> rw [hs] at hr hstep1 <;> dsimp only at hr hstep1
        · cases hr
        · by_cases hbool : opt.kind == .bool <;> simp only [hbool, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind] at hr hstep1 <;> cases hrest : Model.renderSingleOpt.renderValueList opt vs with | error _ => rw [hrest] at hr; cases hr | ok _ => rw [hrest] at hr; injection hr with htoks; subst htoks; rw [parseTokensLoop_append rootName [] _ _ st _ hstep1]; exact ih _ _ heff hprops ho hvs_match hp had hrest
      · by_cases hbool : opt.kind == .bool <;> simp only [hbool, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind] at hr hstep1 <;> cases hrest : Model.renderSingleOpt.renderValueList opt vs with | error _ => rw [hrest] at hr; cases hr | ok _ => rw [hrest] at hr; injection hr with htoks; subst htoks; rw [parseTokensLoop_append rootName [] _ _ st _ hstep1]; exact ih _ _ heff hprops ho hvs_match hp had hrest
private theorem parseTokensLoop_renderSingleOpt {ver : Option String} (rootName : String) (st : Internal.ParseState) (opt : OptSpec) (vals : List OptValue) (toks : List String)
    (heff : st.effectiveVersion = (st.curSpec.version <|> ver)) (hprops : NodeProps st.curSpec st.inheritedGlobals ver) (ho : opt ∈ st.inheritedGlobals ++ st.curSpec.options)
    (hmatch : ∀ v ∈ vals, OptValueMatchesKind opt.kind v) (hlen : opt.repeatable = false → vals.length ≤ 1) (hp : st.pendingOpt = none) (had : st.afterDashDash = false) (hr : Model.renderSingleOpt opt vals = .ok toks) :
    ∃ delta : List OptValue, Internal.parseTokensLoop rootName [] st toks = .ok { st with cliOpts := recordCliOptMany st.cliOpts opt.name delta } ∧
      (if (vals.isEmpty || (opt.kind == .bool && !opt.repeatable && opt.long.isNone && (vals == [.bool false]))) then delta = [] else delta = vals) := by
  have hloc := hprops.validOpts opt ho; unfold Model.renderSingleOpt at hr
  by_cases hempty : vals.isEmpty
  · simp only [hempty, ↓reduceIte, Except.ok.injEq] at hr; subst hr; refine ⟨[], ?_, by simp [hempty]⟩; cases st; simp only at hp; subst hp; simp [recordCliOptMany, Internal.parseTokensLoop]
  · simp only [hempty, Bool.false_eq_true, ↓reduceIte] at hr
    by_cases hbnr : (opt.kind == .bool && !opt.repeatable)
    · simp only [hbnr, ↓reduceIte] at hr; have hk := valueKind_eq_of_beq ((Bool.and_eq_true _ _).mp hbnr).1; have hnr : opt.repeatable = false := by simpa using ((Bool.and_eq_true _ _).mp hbnr).2
      cases vals with
      | nil => cases hempty rfl
      | cons v vs =>
        cases vs with
      | cons _ _ => have hle := hlen hnr; simp at hle
      | nil =>
        have hmv := hmatch v (by simp); cases hv : v with
        | bool b =>
          subst hv; cases b with
          | true =>
            dsimp only at hr; cases hl : opt.long with
            | some l => rw [hl] at hr; injection hr with htoks; subst htoks; have h1 := stepToken_longBool rootName st opt l true hprops.nodupLongs hloc ho hl hk (fun hc => by cases hc) hp had; simp only [↓reduceIte] at h1; refine ⟨[.bool true], ?_, by simp⟩; unfold Internal.parseTokensLoop; rw [h1]; rfl
            | none =>
              rw [hl] at hr; dsimp only at hr; cases hs : opt.short with
              | none => rw [hs] at hr; cases hr
              | some c =>
                rw [hs] at hr; injection hr with htoks; subst htoks; have h1 := stepToken_short_aux rootName st opt c heff hprops ho hs hp had
                have hvb : (opt.kind == .bool) = true := by rw [hk]; rfl
                simp only [hvb, ↓reduceIte] at h1; have hvv : ([OptValue.bool true] == [OptValue.bool false]) = false := rfl; refine ⟨[.bool true], ?_, by simp [hvv]⟩; unfold Internal.parseTokensLoop; rw [h1]; rfl
          | false =>
            dsimp only at hr; cases hl : opt.long with
            | some l => rw [hl] at hr; injection hr with htoks; subst htoks; have h1 := stepToken_longBool rootName st opt l false hprops.nodupLongs hloc ho hl hk (fun _ => hnr) hp had; simp only [Bool.false_eq_true, ↓reduceIte] at h1; refine ⟨[.bool false], ?_, by simp⟩; unfold Internal.parseTokensLoop; rw [h1]; rfl
            | none =>
              rw [hl] at hr; dsimp only at hr; have hvb : (opt.kind == .bool) = true := by rw [hk]; rfl
              have hvv : ([OptValue.bool false] == [OptValue.bool false]) = true := rfl; cases hdef : opt.default with
              | none => rw [hdef] at hr; injection hr with htoks; subst htoks; refine ⟨[], ?_, by simp [hvb, hnr, hvv]⟩; cases st; simp only at hp; subst hp; simp [recordCliOptMany, Internal.parseTokensLoop]
              | some d =>
                rw [hdef] at hr; dsimp only at hr; by_cases hpb : (Model.parseBoolString d == some true); · simp [hpb] at hr
                · have hpbF := Bool.eq_false_iff.mpr hpb; simp only [hpbF, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hr; subst hr; refine ⟨[], ?_, by simp [hvb, hnr, hvv]⟩; cases st; simp only at hp; subst hp; simp [recordCliOptMany, Internal.parseTokensLoop]
        | _ => rw [hk, hv] at hmv; cases hmv
    · simp only [hbnr, Bool.false_eq_true, ↓reduceIte] at hr; refine ⟨vals, parseTokensLoop_renderValueList rootName st opt vals toks heff hprops ho hmatch hp had hr, ?_⟩
      have hn : (vals.isEmpty || (opt.kind == .bool && !opt.repeatable && opt.long.isNone && (vals == [.bool false]))) = false := by
        have hbnrF := Bool.eq_false_iff.mpr hbnr; have hemptyF := Bool.eq_false_iff.mpr hempty; rw [hemptyF, Bool.false_or]; cases h1 : (opt.kind == .bool) <;> cases h2 : opt.repeatable <;> simp_all
      simp [hn]
private theorem renderOpts_cons (parsed : ParsedCmd) (opt : OptSpec) (rest : List OptSpec) :
    Model.renderArgs.renderOpts parsed (opt :: rest) = (let vals := lookupCli parsed.options opt.name; do let headToks ← Model.renderSingleOpt opt vals; let tailToks ← Model.renderArgs.renderOpts parsed rest; .ok (headToks ++ tailToks)) := by cases rest <;> rfl
private theorem parseTokensLoop_renderOpts {ver : Option String} (rootName : String) (st : Internal.ParseState) (parsed : ParsedCmd) (opts : List OptSpec) (toks : List String)
    (heff : st.effectiveVersion = (st.curSpec.version <|> ver)) (hprops : NodeProps st.curSpec st.inheritedGlobals ver) (hndOpts : (opts.map (·.name)).Nodup)
    (hsub : ∀ opt ∈ opts, opt ∈ st.inheritedGlobals ++ st.curSpec.options) (hmatch : ∀ opt ∈ opts, ∀ v ∈ lookupCli parsed.options opt.name, OptValueMatchesKind opt.kind v)
    (hlen : ∀ opt ∈ opts, opt.repeatable = false → (lookupCli parsed.options opt.name).length ≤ 1) (hfresh : ∀ opt ∈ opts, lookupCli st.cliOpts opt.name = [])
    (hp : st.pendingOpt = none) (had : st.afterDashDash = false) (hr : Model.renderArgs.renderOpts parsed opts = .ok toks) :
    ∃ cliFinal, Internal.parseTokensLoop rootName [] st toks = .ok { st with cliOpts := cliFinal } ∧
      (∀ opt ∈ opts, let vals := lookupCli parsed.options opt.name; if (vals.isEmpty || (opt.kind == .bool && !opt.repeatable && opt.long.isNone && (vals == [.bool false]))) then lookupCli cliFinal opt.name = [] else lookupCli cliFinal opt.name = vals.reverse) ∧
      (∀ k, (∀ o' ∈ opts, o'.name ≠ k) → lookupCli cliFinal k = lookupCli st.cliOpts k) := by
  induction opts generalizing st toks with
  | nil => have hnil : Model.renderArgs.renderOpts parsed [] = .ok [] := rfl; rw [hnil] at hr; injection hr with heq; subst heq; refine ⟨st.cliOpts, ?_, (fun _ h => by cases h), (fun _ _ => rfl)⟩; cases st; simp only at hp; subst hp; rfl
  | cons opt rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hndOpts; rw [renderOpts_cons] at hr; dsimp only at hr
    cases hhead : Model.renderSingleOpt opt (lookupCli parsed.options opt.name) with
    | error _ => rw [hhead] at hr; cases hr
    | ok headToks =>
      rw [hhead] at hr; cases htail : Model.renderArgs.renderOpts parsed rest with
      | error _ => rw [htail] at hr; cases hr
      | ok tailToks =>
        rw [htail] at hr; simp only [Bind.bind, Except.bind, Except.ok.injEq] at hr; subst hr
        rcases parseTokensLoop_renderSingleOpt rootName st opt (lookupCli parsed.options opt.name) headToks heff hprops (hsub opt (by simp)) (hmatch opt (by simp)) (hlen opt (by simp)) hp had hhead with ⟨delta, h1, hdelta⟩
        have hfresh_rest : ∀ o' ∈ rest, lookupCli (recordCliOptMany st.cliOpts opt.name delta) o'.name = [] := fun o' ho' => by rw [recordCliOptMany_lookupCli_ne _ _ _ _ (fun heq => hndOpts.1 ⟨o', ho', heq⟩)]; exact hfresh o' (by simp [ho'])
        rcases ih { st with cliOpts := recordCliOptMany st.cliOpts opt.name delta } tailToks heff hprops hndOpts.2 (fun o' ho' => hsub o' (by simp [ho'])) (fun o' ho' => hmatch o' (by simp [ho'])) (fun o' ho' => hlen o' (by simp [ho'])) hfresh_rest hp had htail with ⟨cliFinal, h2, hres, hk_rest⟩
        refine ⟨cliFinal, by rw [parseTokensLoop_append rootName [] headToks tailToks st _ h1]; exact h2, ?_, fun k hk => by rw [hk_rest k (fun o' ho' => hk o' (by simp [ho']))]; exact recordCliOptMany_lookupCli_ne st.cliOpts opt.name k delta (hk opt (by simp)).symm⟩
        intro o' ho'; rcases List.mem_cons.mp ho' with rfl | hmem
        · rw [hk_rest o'.name (fun x hx heq => hndOpts.1 ⟨x, hx, heq⟩)]; dsimp only; rw [recordCliOptMany_lookupCli_same, hfresh o' (by simp), List.append_nil]; split at hdelta <;> simp [*]
        · exact hres o' hmem
private theorem parseTokensLoop_pos_afterDashDash (rootName : String) (st : Internal.ParseState) (pos : List String) (had : st.afterDashDash = true) (hp : st.pendingOpt = none) :
    Internal.parseTokensLoop rootName [] st pos = .ok { st with rawPositionals := pos.reverse ++ st.rawPositionals } := by
  induction pos generalizing st with | nil => cases st; simp only at hp; subst hp; simp [Internal.parseTokensLoop] | cons tok _ ih => unfold Internal.parseTokensLoop Internal.stepToken; simp only [hp, had, ↓reduceIte, Bind.bind, Except.bind]; simpa [had, hp, List.append_assoc] using ih { st with rawPositionals := tok :: st.rawPositionals } had hp
private theorem parseTokensLoop_pos_noDash (rootName : String) (st : Internal.ParseState) (pos : List String) (hleaf : st.curSpec.subcommands.isEmpty = true)
    (hnd : pos.any Model.startsWithDash = false) (hp : st.pendingOpt = none) (had : st.afterDashDash = false) :
    Internal.parseTokensLoop rootName [] st pos = .ok { st with rawPositionals := pos.reverse ++ st.rawPositionals } := by
  induction pos generalizing st with
  | nil => cases st; simp only at hp; subst hp; simp [Internal.parseTokensLoop]
  | cons tok rest ih =>
    have htok_nd : Model.startsWithDash tok = false := by have := List.any_eq_false.mp hnd tok (by simp); cases h : Model.startsWithDash tok <;> simp_all
    have hrest_nd : rest.any Model.startsWithDash = false := List.any_eq_false.mpr (fun x hx => List.any_eq_false.mp hnd x (by simp [hx]))
    have hnodash : ∀ cs, tok.toList ≠ '-' :: cs := fun cs heq => by unfold Model.startsWithDash at htok_nd; rw [heq] at htok_nd; cases htok_nd
    have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList tok (fun heq => hnodash ['-'] heq) (fun heq => hnodash ['-', 'h', 'e', 'l', 'p'] heq) (fun heq => hnodash ['-', 'v', 'e', 'r', 's', 'i', 'o', 'n'] heq)
    have hstep : Internal.stepToken rootName [] st tok = .ok { st with rawPositionals := tok :: st.rawPositionals } := by
      unfold Internal.stepToken; simp only [hp, had, beq_false_of_ne hne_dd, beq_false_of_ne hne_help, beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split <;> first | (rename_i _ heqm; unfold Model.startsWithDash at htok_nd; rw [heqm] at htok_nd; cases htok_nd) | (rename_i _ _ _ heqm; unfold Model.startsWithDash at htok_nd; rw [heqm] at htok_nd; cases htok_nd) | simp [hleaf]
    unfold Internal.parseTokensLoop; simp only [hstep, Bind.bind, Except.bind]; simpa [List.append_assoc] using ih { st with rawPositionals := tok :: st.rawPositionals } hleaf hrest_nd hp had
private theorem parseTokensLoop_posTokens (rootName : String) (st : Internal.ParseState) (pos : List String) (hleaf : st.curSpec.subcommands.isEmpty = true) (hp : st.pendingOpt = none) (had : st.afterDashDash = false) :
    Internal.parseTokensLoop rootName [] st (if pos.any Model.startsWithDash then "--" :: pos else pos) = .ok { st with afterDashDash := pos.any Model.startsWithDash, rawPositionals := pos.reverse ++ st.rawPositionals } := by
  by_cases hd : pos.any Model.startsWithDash
  · simp only [hd, ↓reduceIte]; unfold Internal.parseTokensLoop Internal.stepToken; simp only [hp, had, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
    have hres := parseTokensLoop_pos_afterDashDash rootName { st with afterDashDash := true, pendingOpt := none } pos rfl rfl; cases st; simp only at hp had; subst hp had; exact hres
  · simp only [hd, Bool.false_eq_true, ↓reduceIte]; have hres := parseTokensLoop_pos_noDash rootName st pos hleaf (Bool.eq_false_iff.mpr hd) hp had; rw [had] at hres; exact hres
/-- `test_cmdline_renderArgs_universalRoundTrip` holds universally for `defaultApi`. -/
theorem allPass_renderArgs_universalRoundTrip : Core.AllPass (test_cmdline_renderArgs_universalRoundTrip defaultApi) := by
  dsimp only [Core.AllPass, Core.AllPassRun, test_cmdline_renderArgs_universalRoundTrip, Bind.bind, Pure.pure, Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert]
  intro spec args hValid; change Model.isValidSpec spec = true at hValid; cases hParse : defaultApi.parse spec args with
  | error _ => dsimp only; exact fun h => False.elim h
  | ok parsed =>
    dsimp only; cases hRender : defaultApi.renderArgs spec parsed with
    | error _ => dsimp only; exact fun h => False.elim h
    | ok rendered =>
      dsimp only; change Internal.parseWith spec args = .ok parsed at hParse; change Internal.renderArgsTR spec parsed = .ok rendered at hRender
      rw [Shared.renderArgsTR_eq] at hRender; have hValidNot : (!Model.isValidSpec spec) = false := by simp [hValid]
      unfold Internal.parseWith at hParse; rw [Shared.parseWithEnvM_eq_spec] at hParse; unfold Internal.parseWithEnvSpecM at hParse; rw [Shared.isValidSpecTR_eq] at hParse
      simp only [hValidNot, Bool.false_eq_true, ↓reduceIte, pure, Bind.bind] at hParse; cases hToks : Internal.parseTokens spec.name [] { curSpec := spec, effectiveVersion := spec.version } args with
      | error _ => rw [hToks] at hParse; cases hParse
      | ok finalState =>
        rw [hToks] at hParse; dsimp only at hParse; cases hNonEmpty : !finalState.curSpec.subcommands.isEmpty with
        | true => simp only [hNonEmpty, ↓reduceIte] at hParse; split at hParse <;> cases hParse
        | false =>
          simp only [hNonEmpty, Bool.false_eq_true, ↓reduceIte] at hParse; have hLeaf : finalState.curSpec.subcommands.isEmpty = true := by cases hc : finalState.curSpec.subcommands.isEmpty <;> simp_all
          rw [resolveOptionsTR_id_eq, resolveArgsTR_eq] at hParse; cases hResOpts : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts [] with
          | error _ => rw [hResOpts] at hParse; cases hParse
          | ok resolvedOpts =>
            rw [hResOpts] at hParse; dsimp only at hParse; cases hResArgs : Model.resolveArgs finalState.curSpec.args finalState.rawPositionals [] with
            | error _ => rw [hResArgs] at hParse; cases hParse
            | ok resolvedArgs =>
              rw [hResArgs] at hParse; injection hParse with hParsedEq; subst hParsedEq; have hv0 : spec.version = (spec.version <|> none) := by cases spec.version <;> rfl
              have hInitInv : ParseStateInv spec { curSpec := spec, effectiveVersion := spec.version } := by
                refine ⟨⟨none, ⟨by simpa [Model.isValidSpec] using hValid, rfl⟩, hv0⟩, ?_, ?_, fun _ hc => by cases hc⟩
                · unfold Model.findSubcommandPath Model.findSubcommandPath.go; exact congrArg (fun v => Except.ok ([], v, spec)) hv0.symm
                · exact ⟨(fun _ hk => absurd rfl hk), (fun _ _ _ hv => by cases hv)⟩
              rcases parseTokens_sound spec { curSpec := spec, effectiveVersion := spec.version } hInitInv args hToks with ⟨⟨⟨vp, hFinalNode, hFinalEff⟩, hFinalPath, hFinalCli, _⟩, _⟩
              have hProps := nodeInv_props hFinalNode; unfold Model.renderArgs at hRender; rw [hValidNot] at hRender; dsimp only [Bind.bind, Except.bind] at hRender; rw [hFinalPath] at hRender; dsimp only at hRender; rw [hNonEmpty] at hRender
              cases hRO : Model.renderArgs.renderOpts { subcommandPath := finalState.subPath, options := resolvedOpts, args := resolvedArgs, rawPositionals := finalState.rawPositionals } (finalState.inheritedGlobals ++ finalState.curSpec.options) with
              | error _ => rw [hRO] at hRender; cases hRender
              | ok optTokens =>
                rw [hRO] at hRender; dsimp only [Bind.bind, Except.bind] at hRender; injection hRender with hRenderedEq; subst hRenderedEq
                have hLookup := resolveOptions_lookup_aux (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts resolvedOpts hProps.nodupNames hFinalCli.2 hResOpts
                let stSub : Internal.ParseState := { curSpec := finalState.curSpec, subPath := finalState.subPath, inheritedGlobals := finalState.inheritedGlobals, effectiveVersion := finalState.effectiveVersion }
                rcases parseTokensLoop_renderOpts spec.name stSub { subcommandPath := finalState.subPath, options := resolvedOpts, args := resolvedArgs, rawPositionals := finalState.rawPositionals } (finalState.inheritedGlobals ++ finalState.curSpec.options) optTokens hFinalEff hProps hProps.nodupNames (fun _ ho => ho) (fun o ho v hv => (hLookup o ho).1 v hv) (fun o ho hnr => (hLookup o ho).2.1 hnr) (fun _ _ => rfl) rfl rfl hRO with ⟨cliFinal, hParseOpts, hCliFinal, _⟩
                have hParseSub := parseTokensLoop_subPath spec finalState.subPath hValid hFinalPath; have hParsePos := parseTokensLoop_posTokens spec.name { stSub with cliOpts := cliFinal } finalState.rawPositionals hLeaf rfl rfl; let cliMapped := cliFinal.map (fun p => (p.1, p.2.reverse))
                have hParseAll : Internal.parseTokens spec.name [] { curSpec := spec, effectiveVersion := spec.version } (finalState.subPath ++ optTokens ++ (if finalState.rawPositionals.any Model.startsWithDash then "--" :: finalState.rawPositionals else finalState.rawPositionals)) =
                    .ok { stSub with cliOpts := cliMapped, afterDashDash := finalState.rawPositionals.any Model.startsWithDash, rawPositionals := finalState.rawPositionals } := by
                  unfold Internal.parseTokens; rw [List.append_assoc, parseTokensLoop_append _ _ _ _ _ _ hParseSub, parseTokensLoop_append _ _ _ _ _ _ hParseOpts, hParsePos]; simp [Bind.bind, Except.bind, stSub, cliMapped]
                have hCongr : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv (finalState.inheritedGlobals ++ finalState.curSpec.options) cliMapped [] = .ok resolvedOpts := by
                  rw [← hResOpts]; apply resolveOptions_congr; intro o ho; have hCF := hCliFinal o ho; have hLo := hLookup o ho; dsimp only at hCF hLo; rw [lookupCli_map_rev cliFinal o.name]
                  by_cases hEmpty : (lookupCli resolvedOpts o.name).isEmpty
                  · have hNil : lookupCli resolvedOpts o.name = [] := by cases hxs : lookupCli resolvedOpts o.name with | nil => rfl | cons _ _ => rw [hxs] at hEmpty; cases hEmpty
                    simp only [hEmpty, Bool.true_or, ↓reduceIte] at hCF; rw [hCF, hLo.2.2.1 hNil]; rfl
                  · by_cases hSpecial : (o.kind == .bool && !o.repeatable && o.long.isNone && (lookupCli resolvedOpts o.name == [.bool false]))
                    · simp only [hSpecial, Bool.or_true, ↓reduceIte] at hCF; rw [hCF, hLo.2.2.2.1 hSpecial]; rfl
                    · have hEmptyF := Bool.eq_false_iff.mpr hEmpty; have hSpecialF := Bool.eq_false_iff.mpr hSpecial
                      simp only [hEmptyF, hSpecialF, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hCF; rw [hCF, List.reverse_reverse, resolveSingleOption_pureNoEnv]
                      have hne : (lookupCli resolvedOpts o.name).isEmpty = false := by cases hxs : lookupCli resolvedOpts o.name with | nil => rw [hxs] at hEmpty; exact absurd rfl hEmpty | cons _ _ => rfl
                      simp only [hne, Bool.not_false, ↓reduceIte]
                      have hlen : (!o.repeatable && decide ((lookupCli resolvedOpts o.name).length > 1)) = false := by cases hrep : o.repeatable <;> first | (have hle := hLo.2.1 hrep; simp [decide_eq_false (Nat.not_lt.mpr hle)]) | simp
                      simp only [hlen, Bool.false_eq_true, ↓reduceIte]; exact (hLo.2.2.2.2 (fun hc => by rw [hc] at hne; cases hne)).symm
                change Internal.parseWith spec _ = _ ∧ True; unfold Internal.parseWith; rw [Shared.parseWithEnvM_eq_spec]; unfold Internal.parseWithEnvSpecM; rw [Shared.isValidSpecTR_eq]
                simp only [hValidNot, Bool.false_eq_true, ↓reduceIte, pure, Bind.bind]; rw [hParseAll]; dsimp only [stSub]; simp only [hNonEmpty, Bool.false_eq_true, ↓reduceIte]; rw [resolveOptionsTR_id_eq, resolveArgsTR_eq, hCongr]; dsimp only; rw [hResArgs]; exact ⟨rfl, trivial⟩
/-- `test_cmdline_renderArgs_universalRoundTrip` is reachable via a concrete witness. -/
theorem canReach_renderArgs_universalRoundTrip : CanReach (test_cmdline_renderArgs_universalRoundTrip defaultApi) := by
  dsimp only [Core.CanReach, Core.CanReachRun, test_cmdline_renderArgs_universalRoundTrip, Bind.bind, Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert]
  refine ⟨{ name := "app" }, [], by decide, ?_⟩
  have hp : defaultApi.parse { name := "app" } [] = .ok {} := by cbv
  have hr : defaultApi.renderArgs { name := "app" } {} = .ok [] := by cbv
  rw [hp]; dsimp only; rw [hr]; dsimp only; rw [hp]; exact ⟨rfl, trivial⟩
end LeanSwe.CmdLine.Proofs

import LeanSwe.CmdLine.Proofs.ParserCore
import LeanSwe.CmdLine.Proofs.ErrorBounds

namespace LeanSwe.CmdLine.Proofs

open Core LeanSwe.CmdLine LeanSwe.CmdLine.Proofs.Shared

/-- Filter `(optName, OptValue)` events matching `name` in forward order. -/
def eventsForOpt (events : List (String × OptValue)) (name : String) : List OptValue :=
  events.filterMap (fun p => if p.1 == name then some p.2 else none)

private theorem eventsForOpt_nil (name : String) : eventsForOpt [] name = [] := rfl

private theorem eventsForOpt_append (e1 e2 : List (String × OptValue)) (name : String) :
    eventsForOpt (e1 ++ e2) name = eventsForOpt e1 name ++ eventsForOpt e2 name := by
  unfold eventsForOpt; exact List.filterMap_append

private theorem eventsForOpt_singleton (n : String) (v : OptValue) (k : String) :
    eventsForOpt [(n, v)] k = if k == n then [v] else [] := by
  unfold eventsForOpt
  simp only [List.filterMap_cons, List.filterMap_nil]
  by_cases h : n = k
  · subst h; simp
  · have h1 : (n == k) = false := beq_false_of_ne h
    have h2 : (k == n) = false := beq_false_of_ne (Ne.symm h)
    simp [h1, h2]

private theorem recordCliOpt_rev_eq (cliOpts : List (String × List OptValue))
    (name : String) (v : OptValue) (k : String) :
    (lookupCli (Internal.recordCliOpt cliOpts name v) k).reverse =
      (lookupCli cliOpts k).reverse ++ eventsForOpt [(name, v)] k := by
  rw [eventsForOpt_singleton]
  by_cases hk : k = name
  · subst hk
    simp [recordCliOpt_lookupCli_same]
  · simp [recordCliOpt_lookupCli_ne _ _ _ _ hk, beq_false_of_ne hk]

private theorem lookupCli_cons_ne {k name : String} {vs : List OptValue}
    {rest : List (String × List OptValue)} (hne : name ≠ k) :
    lookupCli ((name, vs) :: rest) k = lookupCli rest k := by
  unfold lookupCli
  simp [beq_false_of_ne hne]

private theorem lookupCli_cliOptsOfPhrases {visibleOpts : List OptSpec}
    (hnd : (visibleOpts.map (·.name)).Nodup) (phrases : List Model.CliPhrase)
    {opt : OptSpec} (ho : opt ∈ visibleOpts) :
    lookupCli (Model.cliOptsOfPhrases visibleOpts phrases) opt.name =
      eventsForOpt (phrases.flatMap Model.CliPhrase.optEvents) opt.name := by
  unfold Model.cliOptsOfPhrases eventsForOpt
  dsimp only
  generalize phrases.flatMap Model.CliPhrase.optEvents = events
  induction visibleOpts with
  | nil => cases ho
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp ho with rfl | htl
    · simp only [List.filterMap_cons]
      by_cases hemp : (events.filterMap fun p => if p.1 == opt.name then some p.2 else none).isEmpty = true
      · simp only [hemp, ↓reduceIte]
        have hnil : (events.filterMap fun p => if p.1 == opt.name then some p.2 else none) = [] :=
          List.isEmpty_iff.mp hemp
        rw [hnil]
        suffices ∀ xs : List OptSpec, (∀ x ∈ xs, x.name ≠ opt.name) →
            lookupCli (xs.filterMap fun o =>
              let vs := events.filterMap fun p => if p.1 == o.name then some p.2 else none
              if vs.isEmpty then none else some (o.name, vs)) opt.name = [] from
          this tl (fun x hx heq => hnd.1 ⟨x, hx, heq⟩)
        intro xs; induction xs with
        | nil => intros; rfl
        | cons x rest ihx =>
          intro hne
          simp only [List.filterMap_cons]
          by_cases hex : (events.filterMap fun p => if p.1 == x.name then some p.2 else none).isEmpty = true
          · simp only [hex, ↓reduceIte]
            exact ihx (fun y hy => hne y (List.Mem.tail _ hy))
          · simp only [hex, Bool.false_eq_true, ↓reduceIte]
            rw [lookupCli_cons_ne (hne x (List.Mem.head _))]
            exact ihx (fun y hy => hne y (List.Mem.tail _ hy))
      · simp only [hemp, Bool.false_eq_true, ↓reduceIte, lookupCli, List.find?_cons, beq_self_eq_true]
    · have hne : hd.name ≠ opt.name := fun heq => hnd.1 ⟨opt, htl, heq.symm⟩
      simp only [List.filterMap_cons]
      by_cases hehd : (events.filterMap fun p => if p.1 == hd.name then some p.2 else none).isEmpty = true
      · simp only [hehd, ↓reduceIte]
        exact ih hnd.2 htl
      · simp only [hehd, Bool.false_eq_true, ↓reduceIte]
        rw [lookupCli_cons_ne hne]
        exact ih hnd.2 htl

/-- `Model.resolveOptions` depends on `cliOpts` only through `lookupCli` on `visibleOpts`. -/
theorem resolveOptions_congr_lookup {getEnv : String → Except CmdLineError (Option String)}
    {visibleOpts : List OptSpec} {cli1 cli2 : List (String × List OptValue)}
    {validators : CustomValidators}
    (h : ∀ opt ∈ visibleOpts, lookupCli cli1 opt.name = lookupCli cli2 opt.name) :
    Model.resolveOptions (m := Id) getEnv visibleOpts cli1 validators =
      Model.resolveOptions (m := Id) getEnv visibleOpts cli2 validators := by
  induction visibleOpts with
  | nil => rfl
  | cons opt rest ih =>
    unfold Model.resolveOptions
    have h1 : lookupCli cli1 opt.name = lookupCli cli2 opt.name := h opt (List.Mem.head _)
    have hrec := ih (fun o ho => h o (List.Mem.tail _ ho))
    change (match Model.resolveSingleOption (m := Id) getEnv opt (lookupCli cli1 opt.name) validators with
      | Except.error e => Except.error e
      | Except.ok resolved? =>
        match Model.resolveOptions (m := Id) getEnv rest cli1 validators with
        | Except.error e => Except.error e
        | Except.ok tail => match resolved? with | none => Except.ok tail | some vals => Except.ok ((opt.name, vals) :: tail)) =
      (match Model.resolveSingleOption (m := Id) getEnv opt (lookupCli cli2 opt.name) validators with
      | Except.error e => Except.error e
      | Except.ok resolved? =>
        match Model.resolveOptions (m := Id) getEnv rest cli2 validators with
        | Except.error e => Except.error e
        | Except.ok tail => match resolved? with | none => Except.ok tail | some vals => Except.ok ((opt.name, vals) :: tail))
    rw [h1, hrec]

/-- Non-empty message helper for string append on the left. -/
theorem nonEmpty_str_append_left {a b : String} (ha : (!a.isEmpty) = true) :
    (!(a ++ b).isEmpty) = true := by
  cases hb : (a ++ b).isEmpty with
  | false => rfl
  | true =>
    have hlen := congrArg String.length (String.isEmpty_iff.mp hb)
    have hz : ("" : String).length = 0 := rfl
    rw [String.length_append, hz] at hlen
    have ha0 : a.length = 0 := by omega
    have hae : a = "" := String.ext_iff.mpr (List.eq_nil_of_length_eq_zero ha0)
    subst hae; cases ha

/-- Every `renderHelpNode` output is non-empty. -/
theorem renderHelpNode_nonEmpty_shared (cmdPath : List String) (visibleOpts : List OptSpec)
    (effectiveVersion : Option String) (targetSpec : CommandSpec) :
    !(Internal.renderHelpNode cmdPath visibleOpts effectiveVersion targetSpec).isEmpty = true := by
  unfold Internal.renderHelpNode
  dsimp only
  cases hb : (let fullCmd := String.intercalate " " cmdPath
    let argUsage := if !targetSpec.subcommands.isEmpty then " <SUBCOMMAND>"
      else String.intercalate "" (targetSpec.args.map fun a =>
        let base := if a.variadic then s!"{a.name}..." else a.name
        if a.required then s!" <{base}>" else s!" [{base}]")
    let usageLine := s!"Usage: {fullCmd} [OPTIONS]{argUsage}"
    let aboutSec := if targetSpec.about.isEmpty then "" else s!"\n\n{targetSpec.about}"
    let subSec := if targetSpec.subcommands.isEmpty then ""
      else "\n\nSUBCOMMANDS:\n" ++ String.intercalate "\n"
        (targetSpec.subcommands.map fun s => if s.about.isEmpty then s!"  {s.name}" else s!"  {s.name}    {s.about}")
    let argsSec := if targetSpec.args.isEmpty then ""
      else "\n\nARGS:\n" ++ String.intercalate "\n"
        (targetSpec.args.map fun a =>
          let tag := if a.variadic then s!"<{a.name}...>" else s!"<{a.name}>"
          if a.help.isEmpty then s!"  {tag}" else s!"  {tag}    {a.help}")
    let optLines := visibleOpts.map fun o =>
      let shortStr := match o.short with | some c => s!"-{c}" | none => "  "
      let longStr := match o.long with
        | some l => if o.short.isSome then s!", --{l}" else s!"--{l}"
        | none => ""
      let valStr := if o.kind == .bool then "" else s!" <{o.valueName.getD "VALUE"}>"
      let head := s!"  {shortStr}{longStr}{valStr}"
      if o.help.isEmpty then head else s!"{head}    {o.help}"
    let helpLine := if targetSpec.shortHelp then "  -h, --help    Print help" else "      --help    Print help"
    let verLines := if effectiveVersion.isSome then
      [if targetSpec.shortVersion then "  -V, --version    Print version" else "      --version    Print version"] else []
    let optsSec := "\n\nOPTIONS:\n" ++ String.intercalate "\n" (optLines ++ [helpLine] ++ verLines)
    usageLine ++ aboutSec ++ subSec ++ argsSec ++ optsSec ++ "\n").isEmpty with
  | false => rfl
  | true =>
    have heq := String.isEmpty_iff.mp hb
    have hlen := congrArg String.length heq
    simp only [String.length_append] at hlen
    have hn : ("\n" : String).length = 1 := rfl
    have hz : ("" : String).length = 0 := rfl
    omega

private theorem renderVersion_nonEmpty (name ver : String) :
    !(Internal.renderVersion name ver).isEmpty = true := by
  unfold Internal.renderVersion
  cases hb : (s!"{name} {ver}\n").isEmpty with
  | false => rfl
  | true =>
    have hlen := congrArg String.length (String.isEmpty_iff.mp hb)
    simp only [toString, String.length_append] at hlen
    have hn : ("\n" : String).length = 1 := rfl
    have hz : ("" : String).length = 0 := rfl
    omega

private theorem parseOptValue_err_props {k : ValueKind} {s : String} {e : CmdLineError}
    (h : Model.parseOptValue k s = .error e) :
    (!e.message.isEmpty) = true ∧ e.kind = .invalidValue := by
  unfold Model.parseOptValue at h
  cases k <;> dsimp only at h
  · cases h
  · cases hb : Model.parseBoolString s with
    | some _ => rw [hb] at h; cases h
    | none =>
      rw [hb] at h; injection h with he; subst he
      exact ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), rfl⟩
  · cases hn : Model.parseNatChars s.toList with
    | some _ => rw [hn] at h; cases h
    | none =>
      rw [hn] at h; injection h with he; subst he
      exact ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), rfl⟩
  · cases hi : Model.parseIntChars s.toList with
    | some _ => rw [hi] at h; cases h
    | none =>
      rw [hi] at h; injection h with he; subst he
      exact ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), rfl⟩
  · split at h
    · cases h
    · injection h with he; subst he
      exact ⟨nonEmpty_str_append_left (nonEmpty_str_append_left (nonEmpty_str_append_left rfl)), rfl⟩
  · cases h

private theorem parseOptValueWith_err_props {k : ValueKind} {s : String} {vs : CustomValidators}
    {e : CmdLineError} (h : Model.parseOptValueWith k s vs = .error e) :
    (!e.message.isEmpty) = true ∧ e.kind = .invalidValue := by
  unfold Model.parseOptValueWith at h
  cases hp : Model.parseOptValue k s with
  | error e0 =>
    rw [hp] at h; simp only [Bind.bind, Except.bind, Except.error.injEq] at h; subst h
    exact parseOptValue_err_props hp
  | ok v =>
    rw [hp] at h; dsimp only [Bind.bind, Except.bind] at h
    unfold Model.validateCustomValue at h
    cases k with
    | custom typeName =>
      dsimp only at h
      cases hfv : vs.find? (fun p => p.1 == typeName) with
      | none => rw [hfv] at h; cases h
      | some pair =>
        rcases pair with ⟨_, check⟩
        rw [hfv] at h; dsimp only at h
        cases hck : check s with
        | ok _ => rw [hck] at h; cases h
        | error msg =>
          rw [hck] at h; dsimp only at h; injection h with he; subst he
          refine ⟨?_, rfl⟩
          dsimp only
          by_cases hm : msg.isEmpty = true
          · simp only [hm, ↓reduceIte]
            exact nonEmpty_str_append_left (nonEmpty_str_append_left (nonEmpty_str_append_left (nonEmpty_str_append_left rfl)))
          · simp [hm]
    | _ => cases h

private theorem splitFirstEq_decomp (s : String) :
    match Internal.splitFirstEq s with
    | (namePart, none) => '=' ∉ s.toList ∧ namePart = s
    | (namePart, some rv) => '=' ∉ namePart.toList ∧ s = namePart ++ "=" ++ rv := by
  unfold Internal.splitFirstEq
  suffices ∀ (rev : List Char) (cs : List Char),
      rev.reverse ++ cs = s.toList → '=' ∉ rev →
      match Internal.splitFirstEq.go s rev cs with
      | (namePart, none) => '=' ∉ s.toList ∧ namePart = s
      | (namePart, some rv) => '=' ∉ namePart.toList ∧ s = namePart ++ "=" ++ rv from
    this [] s.toList rfl (by simp)
  intro rev cs; induction cs generalizing rev with
  | nil =>
    intro hcat hno
    unfold Internal.splitFirstEq.go
    rw [List.append_nil] at hcat
    refine ⟨?_, rfl⟩
    rw [← hcat, List.mem_reverse]; exact hno
  | cons c rest ih =>
    intro hcat hno
    unfold Internal.splitFirstEq.go
    by_cases hc : c = '='
    · subst hc
      simp only [beq_self_eq_true, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [String.toList_ofList, List.mem_reverse]; exact hno
      · apply String.ext_iff.mpr
        rw [← hcat, String.toList_append, String.toList_append,
          String.toList_ofList, String.toList_ofList]
        simp [List.append_assoc]
    · simp only [beq_false_of_ne hc, Bool.false_eq_true, ↓reduceIte]
      apply ih (c :: rev)
      · simpa [List.append_assoc] using hcat
      · intro hm; rcases List.mem_cons.mp hm with rfl | hr
        · exact hc rfl
        · exact hno hr

private theorem parseShortBundle_boolPrefix_append {vp : Option String}
    {curSpec : CommandSpec} {globals : List OptSpec} {effVer : Option String}
    (hprops : NodeProps curSpec globals vp)
    (heff : effVer = (curSpec.version <|> vp))
    (rootName : String) (subPath : List String) (validators : CustomValidators)
    (cliOpts : List (String × List OptValue))
    (pcs : List Char) (pnames : List String) (rem : List Char)
    (hvalid : Model.validShortBoolPrefixBool (globals ++ curSpec.options) pcs pnames = true) :
    ∃ midCli : List (String × List OptValue),
      (∀ k, (lookupCli midCli k).reverse =
        (lookupCli cliOpts k).reverse ++ eventsForOpt (pnames.map (fun n => (n, OptValue.bool true))) k) ∧
      Internal.parseShortBundle (globals ++ curSpec.options) curSpec.shortHelp curSpec.shortVersion
        rootName subPath effVer curSpec validators cliOpts (pcs ++ rem) =
      Internal.parseShortBundle (globals ++ curSpec.options) curSpec.shortHelp curSpec.shortVersion
        rootName subPath effVer curSpec validators midCli rem := by
  induction pcs generalizing pnames cliOpts with
  | nil =>
    cases pnames with
    | nil =>
      refine ⟨cliOpts, fun k => by simp [eventsForOpt], rfl⟩
    | cons _ _ => simp [Model.validShortBoolPrefixBool] at hvalid
  | cons c cs ih =>
    cases pnames with
    | nil => simp [Model.validShortBoolPrefixBool] at hvalid
    | cons n ns =>
      unfold Model.validShortBoolPrefixBool at hvalid
      rw [Bool.and_eq_true] at hvalid
      rcases hvalid with ⟨hhead, htail⟩
      cases hf : (globals ++ curSpec.options).find? (fun o => o.short == some c) with
      | none => rw [hf] at hhead; cases hhead
      | some o =>
        rw [hf] at hhead
        rw [Bool.and_eq_true] at hhead
        have hkind_b : (o.kind == .bool) = true := hhead.1
        have hname_eq : o.name = n := beq_iff_eq.mp hhead.2
        have ho_mem : o ∈ globals ++ curSpec.options := List.mem_of_find?_eq_some hf
        have ho_short : o.short = some c :=
          beq_iff_eq.mp (List.find?_some (p := fun (x : OptSpec) => x.short == some c) hf)
        have hc_in_shorts : c ∈ (globals ++ curSpec.options).filterMap (·.short) :=
          List.mem_filterMap.mpr ⟨o, ho_mem, ho_short⟩
        have hnh : (c == 'h' && curSpec.shortHelp) = false := by
          cases hsh : curSpec.shortHelp
          · simp
          · by_cases hch : c = 'h'
            · subst hch; exact absurd hc_in_shorts (hprops.noShortHelp hsh)
            · simp [beq_false_of_ne hch]
        have hnV : (c == 'V' && curSpec.shortVersion && effVer.isSome) = false := by
          rw [heff]
          cases hsv : (curSpec.shortVersion && (curSpec.version <|> vp).isSome)
          · cases h1 : curSpec.shortVersion <;> cases h2 : (curSpec.version <|> vp).isSome <;> simp_all
          · by_cases hcV : c = 'V'
            · subst hcV; exact absurd hc_in_shorts (hprops.noShortVer hsv)
            · simp [beq_false_of_ne hcV]
        let cli1 := Internal.recordCliOpt cliOpts o.name (.bool true)
        obtain ⟨midCli, hmid_lkp, hmid_eq⟩ := ih cli1 ns htail
        refine ⟨midCli, fun k => ?_, ?_⟩
        · rw [hmid_lkp k, recordCliOpt_rev_eq, hname_eq, List.map_cons,
            show (n, OptValue.bool true) :: List.map (fun x => (x, OptValue.bool true)) ns =
              [(n, OptValue.bool true)] ++ List.map (fun x => (x, OptValue.bool true)) ns from rfl,
            eventsForOpt_append, List.append_assoc]
        · simp only [List.cons_append]
          conv => lhs; unfold Internal.parseShortBundle
          simp only [hnh, hnV, hf, hkind_b, Bool.false_eq_true, ↓reduceIte]
          exact hmid_eq

private theorem shortPrefix_head_ne_dash {visibleOpts : List OptSpec}
    (hvalidOpts : ∀ o ∈ visibleOpts, Model.isValidOptLocal o = true)
    {pcs : List Char} {pnames : List String} {c : Char} {rest : List Char}
    (hpcs : Model.validShortBoolPrefixBool visibleOpts pcs pnames = true)
    (hhead : pcs = c :: rest) : c ≠ '-' := by
  subst hhead
  cases pnames with
  | nil => simp [Model.validShortBoolPrefixBool] at hpcs
  | cons n ns =>
    unfold Model.validShortBoolPrefixBool at hpcs
    rw [Bool.and_eq_true] at hpcs
    cases hf : visibleOpts.find? (fun o => o.short == some c) with
    | none => rw [hf] at hpcs; cases hpcs.1
    | some o =>
      have ho := List.mem_of_find?_eq_some hf
      have hs := beq_iff_eq.mp (List.find?_some (p := fun (x : OptSpec) => x.short == some c) hf)
      exact isValidOptLocal_short_ne_dash (hvalidOpts o ho) hs

private theorem parseTokensLoop_afterDashDash (rootName : String) (validators : CustomValidators)
    (st : Internal.ParseState) (tail : List String)
    (hp : st.pendingOpt = none) (had : st.afterDashDash = true) :
    Internal.parseTokensLoop rootName validators st tail =
      .ok { st with rawPositionals := tail.reverse ++ st.rawPositionals } := by
  induction tail generalizing st with
  | nil =>
    cases st; simp [Internal.parseTokensLoop]
  | cons tok rest ih =>
    cases st with
    | mk curSpec subPath inheritedGlobals effectiveVersion afterDashDash pendingOpt cliOpts rawPositionals =>
      dsimp only at hp had
      subst hp had
      unfold Internal.parseTokensLoop Internal.stepToken
      dsimp only [↓reduceIte, Bind.bind, Except.bind]
      have hrec := ih { curSpec := curSpec, subPath := subPath, inheritedGlobals := inheritedGlobals,
                        effectiveVersion := effectiveVersion, afterDashDash := true, pendingOpt := none,
                        cliOpts := cliOpts, rawPositionals := tok :: rawPositionals } rfl rfl
      simpa [List.reverse_cons, List.append_assoc] using hrec

private theorem singlePhrase_sound {rootSpec : CommandSpec} {validators : CustomValidators}
    {st : Internal.ParseState} {p : Model.CliPhrase}
    {nextG : List OptSpec} {nextVer : Option String} {nextSpec : CommandSpec}
    {nextSeenPos mustEnd : Bool}
    (hinv : ParseStateInv rootSpec st)
    (hp_none : st.pendingOpt = none)
    (had_false : st.afterDashDash = false)
    (hstep : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
      st.curSpec (!st.rawPositionals.isEmpty) p =
      some (nextG, nextVer, nextSpec, nextSeenPos, mustEnd)) :
    ∃ nextSt : Internal.ParseState,
      Internal.parseTokensLoop rootSpec.name validators st p.tokens = .ok nextSt ∧
      nextSt.curSpec = nextSpec ∧
      nextSt.inheritedGlobals = nextG ∧
      nextSt.effectiveVersion = nextVer ∧
      nextSt.subPath = st.subPath ++ (match p.subcmd? with | some s => [s] | none => []) ∧
      nextSt.pendingOpt = none ∧
      nextSt.afterDashDash = mustEnd ∧
      nextSt.rawPositionals = p.posTokens.reverse ++ st.rawPositionals ∧
      (!nextSt.rawPositionals.isEmpty) = nextSeenPos ∧
      (∀ k, (lookupCli nextSt.cliOpts k).reverse =
        (lookupCli st.cliOpts k).reverse ++ eventsForOpt p.optEvents k) := by
  rcases hinv with ⟨⟨vp, hnode, heff⟩, hpath, hcli, _⟩
  have hprops := nodeInv_props hnode
  let visibleOpts := st.inheritedGlobals ++ st.curSpec.options
  cases p with
  | subcommand name =>
    unfold Model.validSinglePhraseStep at hstep
    dsimp only at hstep
    by_cases hcond : (!st.curSpec.subcommands.isEmpty && !!st.rawPositionals.isEmpty) = true
    · simp only [hcond, ↓reduceIte] at hstep
      cases hfs : st.curSpec.subcommands.find? (fun s => s.name == name) with
      | none => rw [hfs] at hstep; cases hstep
      | some sub =>
        rw [hfs] at hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        rcases hstep with ⟨rfl, rfl, rfl, rfl, rfl⟩
        have hmem := List.mem_of_find?_eq_some hfs
        have hsubNode := nodeInv_sub hnode hmem
        have hsubProps := nodeInv_props hsubNode
        have hnameEq : sub.name = name :=
          beq_iff_eq.mp (List.find?_some (p := fun (s : CommandSpec) => s.name == name) hfs)
        have ⟨hne, hnodash⟩ := isValidCommandName_props hsubProps.validName
        rw [hnameEq] at hne hnodash
        have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList name
          (fun heq => hnodash ['-'] heq)
          (fun heq => hnodash ['-', 'h', 'e', 'l', 'p'] heq)
          (fun heq => hnodash ['-', 'v', 'e', 'r', 's', 'i', 'o', 'n'] heq)
        have hsc_pos : (!st.curSpec.subcommands.isEmpty && st.rawPositionals.isEmpty) = true := by
          simpa using hcond
        refine ⟨{ curSpec := sub, subPath := st.subPath ++ [sub.name],
                  inheritedGlobals := st.inheritedGlobals ++ st.curSpec.options,
                  effectiveVersion := sub.version <|> st.effectiveVersion,
                  afterDashDash := false, pendingOpt := none,
                  cliOpts := st.cliOpts, rawPositionals := [] }, ?_,
          rfl, rfl, rfl, by simp [Model.CliPhrase.subcmd?, hnameEq], rfl, rfl,
          by simp only [Bool.and_eq_true, Bool.not_not] at hcond; rw [List.isEmpty_iff.mp hcond.2]; rfl,
          rfl, fun k => by simp [Model.CliPhrase.optEvents, eventsForOpt]⟩
        unfold Model.CliPhrase.tokens Internal.parseTokensLoop Internal.stepToken
        simp only [hp_none, had_false, beq_false_of_ne hne_dd, beq_false_of_ne hne_help,
          beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        cases htl : name.toList with
        | nil => exact absurd htl hne
        | cons c1 rest1 =>
          have hc1n : c1 ≠ '-' := fun heq => by subst heq; exact hnodash _ htl
          split
          · rename_i _ heqm; exact absurd (List.cons.inj heqm).1 hc1n
          · rename_i _ _ _ heqm; exact absurd (List.cons.inj heqm).1 hc1n
          · simp [hsc_pos, hfs, Bind.bind, Except.bind, Internal.parseTokensLoop]
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hstep; cases hstep
  | longBoolTrue l oname =>
    unfold Model.validSinglePhraseStep at hstep
    dsimp only at hstep
    cases hf : (st.inheritedGlobals ++ st.curSpec.options).find? (fun o => o.long == some l) with
    | none => rw [hf] at hstep; cases hstep
    | some o =>
      rw [hf] at hstep; dsimp only at hstep
      by_cases hok : (o.kind == .bool && o.name == oname) = true
      rotate_left; · simp [hok] at hstep
      simp only [hok, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
      rcases hstep with ⟨rfl, rfl, rfl, rfl, rfl⟩
      rw [Bool.and_eq_true] at hok
      have hk_eq : o.kind = .bool := valueKind_eq_of_beq hok.1
      have hname_eq : o.name = oname := beq_iff_eq.mp hok.2
      have ho := List.mem_of_find?_eq_some hf
      have hl : o.long = some l :=
        beq_iff_eq.mp (List.find?_some (p := fun (x : OptSpec) => x.long == some l) hf)
      have hloc := hprops.validOpts o ho
      have ⟨hlne, hlhelp, hlver, hleq, _, _⟩ := isValidOptLocal_long_props hloc hl
      have hlist : ("--" ++ l).toList = '-' :: '-' :: l.toList := by rw [String.toList_append]; rfl
      have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList ("--" ++ l)
        (fun heq => by rw [hlist] at heq; exact hlne (List.cons.inj (List.cons.inj heq).2).2)
        (fun heq => by rw [hlist] at heq; exact hlhelp (by have := congrArg String.ofList (List.cons.inj (List.cons.inj heq).2).2; simpa [String.ofList_toList] using this))
        (fun heq => by rw [hlist] at heq; exact hlver (by have := congrArg String.ofList (List.cons.inj (List.cons.inj heq).2).2; simpa [String.ofList_toList] using this))
      have hlkp := lookupLongOpt_pos (st.inheritedGlobals ++ st.curSpec.options) hprops.nodupLongs ho hl
      have hsf : Internal.splitFirstEq (String.ofList l.toList) = (l, none) := by
        rw [String.ofList_toList]; exact splitFirstEq_none l hleq
      have hnie : l.isEmpty = false := by cases hc : l.toList <;> simp_all [String.isEmpty]
      have hnhv : ((l == "help") || (l == "version" && st.effectiveVersion.isSome)) = false := by
        simp [beq_false_of_ne hlhelp, beq_false_of_ne hlver]
      refine ⟨{ st with cliOpts := Internal.recordCliOpt st.cliOpts o.name (.bool true) }, ?_,
        rfl, rfl, rfl, by simp [Model.CliPhrase.subcmd?], hp_none, had_false,
        by simp [Model.CliPhrase.posTokens], rfl,
        fun k => by simpa [Model.CliPhrase.optEvents, hname_eq] using recordCliOpt_rev_eq st.cliOpts o.name (.bool true) k⟩
      unfold Model.CliPhrase.tokens Internal.parseTokensLoop Internal.stepToken
      simp only [hp_none, had_false, beq_false_of_ne hne_dd, beq_false_of_ne hne_help,
        beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i longRest heq; rw [hlist] at heq
        have hlr := (List.cons.inj (List.cons.inj heq).2).2
        rw [← hlr, hsf]
        simp [hnie, hnhv, hlkp, hok.1, Bind.bind, Except.bind, Internal.parseTokensLoop]
      · rename_i _ _ h1 heq; rw [hlist] at heq
        injection heq with _ h2; injection h2 with hc _; subst hc; exact False.elim (h1 rfl)
      · rename_i _ h1 _; exact False.elim (h1 _ hlist)
  | longBoolNeg b oname =>
    unfold Model.validSinglePhraseStep at hstep
    dsimp only at hstep
    cases hf : (st.inheritedGlobals ++ st.curSpec.options).find? (fun o => o.long == some b) with
    | none => rw [hf] at hstep; cases hstep
    | some o =>
      rw [hf] at hstep; dsimp only at hstep
      by_cases hok : (o.kind == .bool && !o.repeatable && o.name == oname) = true
      rotate_left; · simp [hok] at hstep
      simp only [hok, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
      rcases hstep with ⟨rfl, rfl, rfl, rfl, rfl⟩
      simp only [Bool.and_eq_true] at hok
      have hk_eq : o.kind = .bool := valueKind_eq_of_beq hok.1.1
      have hnr : o.repeatable = false := by simpa using hok.1.2
      have hname_eq : o.name = oname := beq_iff_eq.mp hok.2
      have ho := List.mem_of_find?_eq_some hf
      have hl : o.long = some b :=
        beq_iff_eq.mp (List.find?_some (p := fun (x : OptSpec) => x.long == some b) hf)
      have hloc := hprops.validOpts o ho
      have ⟨_, _, _, hleq, _, _⟩ := isValidOptLocal_long_props hloc hl
      have hlist : ("--no-" ++ b).toList = '-' :: '-' :: ('n' :: 'o' :: '-' :: b.toList) := by
        rw [String.toList_append]; rfl
      have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList ("--no-" ++ b)
        (fun heq => by rw [hlist] at heq; cases heq)
        (fun heq => by rw [hlist] at heq; cases heq)
        (fun heq => by rw [hlist] at heq; cases heq)
      have hlkp := lookupLongOpt_neg (st.inheritedGlobals ++ st.curSpec.options) hprops.nodupLongs ho hk_eq hnr hl
      have hno_eq : '=' ∉ ("no-" ++ b).toList := by
        rw [String.toList_append]; change '=' ∉ ['n', 'o', '-'] ++ b.toList; simp [hleq]
      have hsf : Internal.splitFirstEq (String.ofList ('n' :: 'o' :: '-' :: b.toList)) = ("no-" ++ b, none) := by
        have h1 : ('n' :: 'o' :: '-' :: b.toList) = ("no-" ++ b).toList := by rw [String.toList_append]; rfl
        rw [h1, String.ofList_toList]; exact splitFirstEq_none ("no-" ++ b) hno_eq
      have hnie : ("no-" ++ b).isEmpty = false := by simp [String.isEmpty]
      have hnhv : (("no-" ++ b == "help") || ("no-" ++ b == "version" && st.effectiveVersion.isSome)) = false := by
        have hn1 : "no-" ++ b ≠ "help" := fun heq => by have := congrArg String.toList heq; simp [String.toList_append] at this
        have hn2 : "no-" ++ b ≠ "version" := fun heq => by have := congrArg String.toList heq; simp [String.toList_append] at this
        simp [beq_false_of_ne hn1, beq_false_of_ne hn2]
      refine ⟨{ st with cliOpts := Internal.recordCliOpt st.cliOpts o.name (.bool false) }, ?_,
        rfl, rfl, rfl, by simp [Model.CliPhrase.subcmd?], hp_none, had_false,
        by simp [Model.CliPhrase.posTokens], rfl,
        fun k => by simpa [Model.CliPhrase.optEvents, hname_eq] using recordCliOpt_rev_eq st.cliOpts o.name (.bool false) k⟩
      unfold Model.CliPhrase.tokens Internal.parseTokensLoop Internal.stepToken
      simp only [hp_none, had_false, beq_false_of_ne hne_dd, beq_false_of_ne hne_help,
        beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i longRest heq; rw [hlist] at heq
        have hlr := (List.cons.inj (List.cons.inj heq).2).2
        rw [← hlr, hsf]
        simp [hnie, hnhv, hlkp, Bind.bind, Except.bind, Internal.parseTokensLoop]
      · rename_i _ _ h1 heq; rw [hlist] at heq
        injection heq with _ h2; injection h2 with hc _; subst hc; exact False.elim (h1 rfl)
      · rename_i _ h1 _; exact False.elim (h1 _ hlist)
  | longBoolEq l rv oname val =>
    unfold Model.validSinglePhraseStep at hstep
    dsimp only at hstep
    cases hf : (st.inheritedGlobals ++ st.curSpec.options).find? (fun o => o.long == some l) with
    | none => rw [hf] at hstep; cases hstep
    | some o =>
      rw [hf] at hstep; dsimp only at hstep
      cases hok : (o.kind == .bool && o.name == oname && !(o.repeatable && !val) &&
          Model.parseBoolString rv == some val) with
      | false => rw [hok] at hstep; cases hstep
      | true =>
      rw [hok] at hstep
      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
      rcases hstep with ⟨rfl, rfl, rfl, rfl, rfl⟩
      simp only [Bool.and_eq_true] at hok
      rcases hok with ⟨⟨⟨hkb, hname_b⟩, hnot_rb⟩, hpbs_b⟩
      have hname_eq : o.name = oname := beq_iff_eq.mp hname_b
      have hpbs : Model.parseBoolString rv = some val := beq_iff_eq.mp hpbs_b
      have ho := List.mem_of_find?_eq_some hf
      have hl : o.long = some l :=
        beq_iff_eq.mp (List.find?_some (p := fun (x : OptSpec) => x.long == some l) hf)
      have ⟨hlne, hlhelp, hlver, hleq, _, _⟩ := isValidOptLocal_long_props (hprops.validOpts o ho) hl
      have hlist : ("--" ++ l ++ "=" ++ rv).toList = '-' :: '-' :: (l.toList ++ ('=' :: rv.toList)) := by
        rw [String.toList_append, String.toList_append, String.toList_append,
          show "--".toList = ['-', '-'] from rfl, show "=".toList = ['='] from rfl]
        simp [List.append_assoc]
      have hmem : '=' ∈ ("--" ++ l ++ "=" ++ rv).toList := by rw [hlist]; simp
      have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList ("--" ++ l ++ "=" ++ rv)
        (fun heq => by have := hmem; rw [heq] at this; simp at this)
        (fun heq => by have := hmem; rw [heq] at this; simp at this)
        (fun heq => by have := hmem; rw [heq] at this; simp at this)
      have hlkp := lookupLongOpt_pos (st.inheritedGlobals ++ st.curSpec.options) hprops.nodupLongs ho hl
      have hsf : Internal.splitFirstEq (String.ofList (l.toList ++ ('=' :: rv.toList))) = (l, some rv) := by
        have heql : String.ofList (l.toList ++ ('=' :: rv.toList)) = l ++ "=" ++ rv := by
          have h1 : (l ++ "=" ++ rv).toList = l.toList ++ ('=' :: rv.toList) := by simp [String.toList_append]
          rw [← h1, String.ofList_toList]
        rw [heql]; exact splitFirstEq_append l rv hleq
      have hnie : l.isEmpty = false := by simp [String.isEmpty]; intro hc; subst hc; exact hlne rfl
      have hnhv : ((l == "help") || (l == "version" && st.effectiveVersion.isSome)) = false := by
        simp [beq_false_of_ne hlhelp, beq_false_of_ne hlver]
      have hrb_f : (o.repeatable && !val) = false := by
        cases hrp : o.repeatable <;> cases val <;> simp [hrp] at hnot_rb ⊢
      have hpv : Model.parseOptValue .bool rv = .ok (.bool val) := by
        unfold Model.parseOptValue; simp [hpbs]
      refine ⟨{ st with cliOpts := Internal.recordCliOpt st.cliOpts o.name (.bool val) }, ?_,
        rfl, rfl, rfl, by simp [Model.CliPhrase.subcmd?], hp_none, had_false,
        by simp [Model.CliPhrase.posTokens], rfl,
        fun k => by simpa [Model.CliPhrase.optEvents, hname_eq] using recordCliOpt_rev_eq st.cliOpts o.name (.bool val) k⟩
      unfold Model.CliPhrase.tokens Internal.parseTokensLoop Internal.stepToken
      simp only [hp_none, had_false, beq_false_of_ne hne_dd, beq_false_of_ne hne_help,
        beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i longRest heq; rw [hlist] at heq
        have hlr := (List.cons.inj (List.cons.inj heq).2).2
        rw [← hlr, hsf]
        simp [hnie, hnhv, hlkp, hkb, Shared.parseOptValueFast_eq, hpv, hrb_f, Bind.bind, Except.bind, Internal.parseTokensLoop]
      · rename_i _ _ h1 heq; rw [hlist] at heq
        injection heq with _ h2; injection h2 with hc _; subst hc; exact False.elim (h1 rfl)
      · rename_i _ h1 _; exact False.elim (h1 _ hlist)
  | longValEq l rv oname val =>
    unfold Model.validSinglePhraseStep at hstep
    dsimp only at hstep
    cases hf : (st.inheritedGlobals ++ st.curSpec.options).find? (fun o => o.long == some l) with
    | none => rw [hf] at hstep; cases hstep
    | some o =>
      rw [hf] at hstep; dsimp only at hstep
      cases hpv : Model.parseOptValueWith o.kind rv validators with
      | error _ => rw [hpv] at hstep; simp at hstep
      | ok v =>
        rw [hpv] at hstep
        cases hok : (o.kind != .bool && o.name == oname && decide (v = val)) with
        | false => rw [hok] at hstep; cases hstep
        | true =>
          rw [hok] at hstep
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl, rfl, rfl, rfl⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
          rcases hok with ⟨⟨hnk_b, hname_b⟩, hveq⟩
          subst v
          have hkb_f : (o.kind == .bool) = false := by
            cases hc : (o.kind == .bool) <;> simp [bne, hc] at hnk_b; rfl
          have hname_eq : o.name = oname := beq_iff_eq.mp hname_b
          have ho := List.mem_of_find?_eq_some hf
          have hl : o.long = some l :=
            beq_iff_eq.mp (List.find?_some (p := fun (x : OptSpec) => x.long == some l) hf)
          have ⟨hlne, hlhelp, hlver, hleq, _, _⟩ := isValidOptLocal_long_props (hprops.validOpts o ho) hl
          have hlist : ("--" ++ l ++ "=" ++ rv).toList = '-' :: '-' :: (l.toList ++ ('=' :: rv.toList)) := by
            rw [String.toList_append, String.toList_append, String.toList_append,
              show "--".toList = ['-', '-'] from rfl, show "=".toList = ['='] from rfl]
            simp [List.append_assoc]
          have hmem : '=' ∈ ("--" ++ l ++ "=" ++ rv).toList := by rw [hlist]; simp
          have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList ("--" ++ l ++ "=" ++ rv)
            (fun heq => by have := hmem; rw [heq] at this; simp at this)
            (fun heq => by have := hmem; rw [heq] at this; simp at this)
            (fun heq => by have := hmem; rw [heq] at this; simp at this)
          have hlkp := lookupLongOpt_pos (st.inheritedGlobals ++ st.curSpec.options) hprops.nodupLongs ho hl
          have hsf : Internal.splitFirstEq (String.ofList (l.toList ++ ('=' :: rv.toList))) = (l, some rv) := by
            have heql : String.ofList (l.toList ++ ('=' :: rv.toList)) = l ++ "=" ++ rv := by
              have h1 : (l ++ "=" ++ rv).toList = l.toList ++ ('=' :: rv.toList) := by simp [String.toList_append]
              rw [← h1, String.ofList_toList]
            rw [heql]; exact splitFirstEq_append l rv hleq
          have hnie : l.isEmpty = false := by simp [String.isEmpty]; intro hc; subst hc; exact hlne rfl
          have hnhv : ((l == "help") || (l == "version" && st.effectiveVersion.isSome)) = false := by
            simp [beq_false_of_ne hlhelp, beq_false_of_ne hlver]
          refine ⟨{ st with cliOpts := Internal.recordCliOpt st.cliOpts o.name val }, ?_,
            rfl, rfl, rfl, by simp [Model.CliPhrase.subcmd?], hp_none, had_false,
            by simp [Model.CliPhrase.posTokens], rfl,
            fun k => by simpa [Model.CliPhrase.optEvents, hname_eq] using recordCliOpt_rev_eq st.cliOpts o.name val k⟩
          unfold Model.CliPhrase.tokens Internal.parseTokensLoop Internal.stepToken
          simp only [hp_none, had_false, beq_false_of_ne hne_dd, beq_false_of_ne hne_help,
            beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          split
          · rename_i longRest heq; rw [hlist] at heq
            have hlr := (List.cons.inj (List.cons.inj heq).2).2
            rw [← hlr, hsf]
            simp [hnie, hnhv, hlkp, hkb_f, parseOptValueWithFast_eq, hpv, Bind.bind, Except.bind, Internal.parseTokensLoop]
          · rename_i _ _ h1 heq; rw [hlist] at heq
            injection heq with _ h2; injection h2 with hc _; subst hc; exact False.elim (h1 rfl)
          · rename_i _ h1 _; exact False.elim (h1 _ hlist)
  | longValSep l rv oname val =>
    unfold Model.validSinglePhraseStep at hstep
    dsimp only at hstep
    cases hf : (st.inheritedGlobals ++ st.curSpec.options).find? (fun o => o.long == some l) with
    | none => rw [hf] at hstep; cases hstep
    | some o =>
      rw [hf] at hstep; dsimp only at hstep
      cases hpv : Model.parseOptValueWith o.kind rv validators with
      | error _ => rw [hpv] at hstep; simp at hstep
      | ok v =>
        rw [hpv] at hstep
        cases hok : (o.kind != .bool && o.name == oname && decide (v = val)) with
        | false => rw [hok] at hstep; cases hstep
        | true =>
          rw [hok] at hstep
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl, rfl, rfl, rfl⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
          rcases hok with ⟨⟨hnk_b, hname_b⟩, hveq⟩
          subst v
          have hkb_f : (o.kind == .bool) = false := by
            cases hc : (o.kind == .bool) <;> simp [bne, hc] at hnk_b; rfl
          have hname_eq : o.name = oname := beq_iff_eq.mp hname_b
          have ho := List.mem_of_find?_eq_some hf
          have hl : o.long = some l :=
            beq_iff_eq.mp (List.find?_some (p := fun (x : OptSpec) => x.long == some l) hf)
          have ⟨hlne, hlhelp, hlver, hleq, _, _⟩ := isValidOptLocal_long_props (hprops.validOpts o ho) hl
          have hlist : ("--" ++ l).toList = '-' :: '-' :: l.toList := by rw [String.toList_append]; rfl
          have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList ("--" ++ l)
            (fun heq => by rw [hlist] at heq; exact hlne (List.cons.inj (List.cons.inj heq).2).2)
            (fun heq => by rw [hlist] at heq; exact hlhelp (by have := congrArg String.ofList (List.cons.inj (List.cons.inj heq).2).2; simpa [String.ofList_toList] using this))
            (fun heq => by rw [hlist] at heq; exact hlver (by have := congrArg String.ofList (List.cons.inj (List.cons.inj heq).2).2; simpa [String.ofList_toList] using this))
          have hlkp := lookupLongOpt_pos (st.inheritedGlobals ++ st.curSpec.options) hprops.nodupLongs ho hl
          have hsf : Internal.splitFirstEq (String.ofList l.toList) = (l, none) := by
            rw [String.ofList_toList]; exact splitFirstEq_none l hleq
          have hnie : l.isEmpty = false := by cases hc : l.toList <;> simp_all [String.isEmpty]
          have hnhv : ((l == "help") || (l == "version" && st.effectiveVersion.isSome)) = false := by
            simp [beq_false_of_ne hlhelp, beq_false_of_ne hlver]
          have hstep1 : Internal.stepToken rootSpec.name validators st ("--" ++ l) = .ok { st with pendingOpt := some o } := by
            unfold Internal.stepToken
            simp only [hp_none, had_false, beq_false_of_ne hne_dd, beq_false_of_ne hne_help,
              beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            split
            · rename_i longRest heq; rw [hlist] at heq
              have hlr := (List.cons.inj (List.cons.inj heq).2).2
              rw [← hlr, hsf]; simp [hnie, hnhv, hlkp, hkb_f]
            · rename_i _ _ h1 heq; rw [hlist] at heq
              injection heq with _ h2; injection h2 with hc _; subst hc; exact False.elim (h1 rfl)
            · rename_i _ h1 _; exact False.elim (h1 _ hlist)
          have hstep2 : Internal.stepToken rootSpec.name validators { st with pendingOpt := some o } rv =
              .ok { st with pendingOpt := none, cliOpts := Internal.recordCliOpt st.cliOpts o.name val } := by
            unfold Internal.stepToken
            simp [parseOptValueWithFast_eq, hpv, Bind.bind, Except.bind]
          refine ⟨{ st with pendingOpt := none, cliOpts := Internal.recordCliOpt st.cliOpts o.name val }, ?_,
            rfl, rfl, rfl, by simp [Model.CliPhrase.subcmd?], rfl, had_false,
            by simp [Model.CliPhrase.posTokens], rfl,
            fun k => by simpa [Model.CliPhrase.optEvents, hname_eq] using recordCliOpt_rev_eq st.cliOpts o.name val k⟩
          unfold Model.CliPhrase.tokens Internal.parseTokensLoop
          rw [hstep1]; dsimp only [Bind.bind, Except.bind]
          unfold Internal.parseTokensLoop
          rw [hstep2]; rfl
  | shortBoolCluster cs onames =>
    unfold Model.validSinglePhraseStep at hstep
    dsimp only at hstep
    by_cases hok : (!cs.isEmpty && Model.validShortBoolPrefixBool (st.inheritedGlobals ++ st.curSpec.options) cs onames) = true
    rotate_left; · simp [hok] at hstep
    simp only [hok, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
    rcases hstep with ⟨rfl, rfl, rfl, rfl, rfl⟩
    rw [Bool.and_eq_true] at hok
    cases hcs : cs with
    | nil => simp [hcs] at hok
    | cons c restCs =>
      have hc_ne : c ≠ '-' := shortPrefix_head_ne_dash hprops.validOpts hok.2 hcs
      have htok_list : (String.ofList ('-' :: c :: restCs)).toList = '-' :: c :: restCs :=
        String.toList_ofList
      have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList (String.ofList ('-' :: c :: restCs))
        (fun heq => by rw [htok_list] at heq; exact hc_ne (List.cons.inj (List.cons.inj heq).2).1)
        (fun heq => by rw [htok_list] at heq; exact hc_ne (List.cons.inj (List.cons.inj heq).2).1)
        (fun heq => by rw [htok_list] at heq; exact hc_ne (List.cons.inj (List.cons.inj heq).2).1)
      have hv_cs : Model.validShortBoolPrefixBool (st.inheritedGlobals ++ st.curSpec.options) (c :: restCs) onames = true :=
        hcs ▸ hok.2
      obtain ⟨midCli, hmid_lkp, hmid_eq⟩ := parseShortBundle_boolPrefix_append hprops heff
        rootSpec.name st.subPath validators st.cliOpts (c :: restCs) onames [] hv_cs
      rw [List.append_nil] at hmid_eq
      have hsb : Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp
          st.curSpec.shortVersion rootSpec.name st.subPath st.effectiveVersion st.curSpec validators
          st.cliOpts (c :: restCs) = .ok (midCli, none) := by
        rw [hmid_eq]; rfl
      refine ⟨{ st with cliOpts := midCli, pendingOpt := none }, ?_,
        rfl, rfl, rfl, by simp [Model.CliPhrase.subcmd?], rfl, had_false,
        by simp [Model.CliPhrase.posTokens], rfl,
        fun k => by simpa [Model.CliPhrase.optEvents] using hmid_lkp k⟩
      unfold Model.CliPhrase.tokens Internal.parseTokensLoop Internal.stepToken
      simp only [hp_none, had_false, beq_false_of_ne hne_dd, beq_false_of_ne hne_help,
        beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [htok_list]
      split
      · rename_i _ heq; exact absurd (List.cons.inj (List.cons.inj heq).2).1 hc_ne
      · rename_i _ c' sr' _ heq
        have hc' := (List.cons.inj (List.cons.inj heq).2).1
        have hsr' := (List.cons.inj (List.cons.inj heq).2).2
        subst hc' hsr'
        simp [hsb, Bind.bind, Except.bind, Internal.parseTokensLoop]
      · rename_i _ _ h2; exact absurd rfl (h2 c restCs)
  | shortAttachedVal pcs pnames oc rv oname val =>
    unfold Model.validSinglePhraseStep at hstep
    dsimp only at hstep
    cases hpre : (!rv.isEmpty && Model.validShortBoolPrefixBool (st.inheritedGlobals ++ st.curSpec.options) pcs pnames) with
    | false => rw [hpre] at hstep; cases hstep
    | true =>
    rw [hpre] at hstep; simp only [↓reduceIte] at hstep
    rw [Bool.and_eq_true] at hpre
    cases hf : (st.inheritedGlobals ++ st.curSpec.options).find? (fun o => o.short == some oc) with
    | none => rw [hf] at hstep; cases hstep
    | some o =>
      rw [hf] at hstep; dsimp only at hstep
      cases hpv : Model.parseOptValueWith o.kind (String.ofList rv) validators with
      | error _ => rw [hpv] at hstep; simp at hstep
      | ok v =>
        rw [hpv] at hstep
        cases hok : (o.kind != .bool && o.name == oname && decide (v = val)) with
        | false => rw [hok] at hstep; cases hstep
        | true =>
          rw [hok] at hstep
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl, rfl, rfl, rfl⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
          rcases hok with ⟨⟨hnk_b, hname_b⟩, hveq⟩
          subst v
          have hkb_f : (o.kind == .bool) = false := by
            cases hc : (o.kind == .bool) <;> simp [bne, hc] at hnk_b; rfl
          have hname_eq : o.name = oname := beq_iff_eq.mp hname_b
          have ho := List.mem_of_find?_eq_some hf
          have hs : o.short = some oc :=
            beq_iff_eq.mp (List.find?_some (p := fun (x : OptSpec) => x.short == some oc) hf)
          have hoc_ne : oc ≠ '-' := isValidOptLocal_short_ne_dash (hprops.validOpts o ho) hs
          have hoc_mem : oc ∈ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short) :=
            List.mem_filterMap.mpr ⟨o, ho, hs⟩
          have hnh : (oc == 'h' && st.curSpec.shortHelp) = false := by
            cases hsh : st.curSpec.shortHelp
            · simp
            · by_cases hch : oc = 'h'
              · subst hch; exact absurd hoc_mem (hprops.noShortHelp hsh)
              · simp [beq_false_of_ne hch]
          have hnV : (oc == 'V' && st.curSpec.shortVersion && st.effectiveVersion.isSome) = false := by
            rw [heff]
            cases hsv : (st.curSpec.shortVersion && (st.curSpec.version <|> vp).isSome)
            · cases h1 : st.curSpec.shortVersion <;> cases h2 : (st.curSpec.version <|> vp).isSome <;> simp_all
            · by_cases hcV : oc = 'V'
              · subst hcV; exact absurd hoc_mem (hprops.noShortVer hsv)
              · simp [beq_false_of_ne hcV]
          obtain ⟨midCli, hmid_lkp, hmid_eq⟩ := parseShortBundle_boolPrefix_append hprops heff
            rootSpec.name st.subPath validators st.cliOpts pcs pnames (oc :: rv) hpre.2
          have hsb_oc : Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp
              st.curSpec.shortVersion rootSpec.name st.subPath st.effectiveVersion st.curSpec validators
              midCli (oc :: rv) = .ok (Internal.recordCliOpt midCli o.name val, none) := by
            unfold Internal.parseShortBundle
            simp [hnh, hnV, hf, hkb_f, hpre.1, parseOptValueWithFast_eq, hpv, Bind.bind, Except.bind]
          obtain ⟨c0, tailCs, hfull_cs, hc0_ne⟩ :
              ∃ c0 tailCs, pcs ++ (oc :: rv) = c0 :: tailCs ∧ c0 ≠ '-' := by
            cases hpcs : pcs with
            | nil => exact ⟨oc, rv, rfl, hoc_ne⟩
            | cons c rest => exact ⟨c, rest ++ (oc :: rv), rfl, shortPrefix_head_ne_dash hprops.validOpts hpre.2 hpcs⟩
          let tok := String.ofList ('-' :: (pcs ++ (oc :: rv)))
          have htok_list : tok.toList = '-' :: c0 :: tailCs := by
            dsimp only [tok]; rw [String.toList_ofList, hfull_cs]
          have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList tok
            (fun heq => by rw [htok_list] at heq; exact hc0_ne (List.cons.inj (List.cons.inj heq).2).1)
            (fun heq => by rw [htok_list] at heq; exact hc0_ne (List.cons.inj (List.cons.inj heq).2).1)
            (fun heq => by rw [htok_list] at heq; exact hc0_ne (List.cons.inj (List.cons.inj heq).2).1)
          have hstep1 : Internal.stepToken rootSpec.name validators st tok =
              .ok { st with cliOpts := Internal.recordCliOpt midCli o.name val, pendingOpt := none } := by
            unfold Internal.stepToken
            simp only [hp_none, had_false, beq_false_of_ne hne_dd, beq_false_of_ne hne_help,
              beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            rw [htok_list]
            split
            · rename_i _ heq; exact absurd (List.cons.inj (List.cons.inj heq).2).1 hc0_ne
            · rename_i _ c' sr' _ heq
              have hc' := (List.cons.inj (List.cons.inj heq).2).1
              have hsr' := (List.cons.inj (List.cons.inj heq).2).2
              subst hc' hsr'
              rw [← hfull_cs, hmid_eq, hsb_oc]; rfl
            · rename_i _ _ h2; exact absurd rfl (h2 c0 tailCs)
          dsimp only [tok] at hstep1
          refine ⟨{ st with cliOpts := Internal.recordCliOpt midCli o.name val, pendingOpt := none }, ?_,
            rfl, rfl, rfl, by simp [Model.CliPhrase.subcmd?], rfl, had_false,
            by simp [Model.CliPhrase.posTokens], rfl, fun k => ?_⟩
          · unfold Model.CliPhrase.tokens Internal.parseTokensLoop
            rw [hstep1]; rfl
          · rw [recordCliOpt_rev_eq, hmid_lkp k, hname_eq, Model.CliPhrase.optEvents,
              eventsForOpt_append, List.append_assoc]
  | shortSepVal pcs pnames oc rv oname val =>
    unfold Model.validSinglePhraseStep at hstep
    dsimp only at hstep
    cases hpre : Model.validShortBoolPrefixBool (st.inheritedGlobals ++ st.curSpec.options) pcs pnames with
    | false => rw [hpre] at hstep; cases hstep
    | true =>
    rw [hpre] at hstep; simp only [↓reduceIte] at hstep
    cases hf : (st.inheritedGlobals ++ st.curSpec.options).find? (fun o => o.short == some oc) with
    | none => rw [hf] at hstep; cases hstep
    | some o =>
      rw [hf] at hstep; dsimp only at hstep
      cases hpv : Model.parseOptValueWith o.kind rv validators with
      | error _ => rw [hpv] at hstep; simp at hstep
      | ok v =>
        rw [hpv] at hstep
        cases hok : (o.kind != .bool && o.name == oname && decide (v = val)) with
        | false => rw [hok] at hstep; cases hstep
        | true =>
          rw [hok] at hstep
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl, rfl, rfl, rfl⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
          rcases hok with ⟨⟨hnk_b, hname_b⟩, hveq⟩
          subst v
          have hkb_f : (o.kind == .bool) = false := by
            cases hc : (o.kind == .bool) <;> simp [bne, hc] at hnk_b; rfl
          have hname_eq : o.name = oname := beq_iff_eq.mp hname_b
          have ho := List.mem_of_find?_eq_some hf
          have hs : o.short = some oc :=
            beq_iff_eq.mp (List.find?_some (p := fun (x : OptSpec) => x.short == some oc) hf)
          have hoc_ne : oc ≠ '-' := isValidOptLocal_short_ne_dash (hprops.validOpts o ho) hs
          have hoc_mem : oc ∈ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short) :=
            List.mem_filterMap.mpr ⟨o, ho, hs⟩
          have hnh : (oc == 'h' && st.curSpec.shortHelp) = false := by
            cases hsh : st.curSpec.shortHelp
            · simp
            · by_cases hch : oc = 'h'
              · subst hch; exact absurd hoc_mem (hprops.noShortHelp hsh)
              · simp [beq_false_of_ne hch]
          have hnV : (oc == 'V' && st.curSpec.shortVersion && st.effectiveVersion.isSome) = false := by
            rw [heff]
            cases hsv : (st.curSpec.shortVersion && (st.curSpec.version <|> vp).isSome)
            · cases h1 : st.curSpec.shortVersion <;> cases h2 : (st.curSpec.version <|> vp).isSome <;> simp_all
            · by_cases hcV : oc = 'V'
              · subst hcV; exact absurd hoc_mem (hprops.noShortVer hsv)
              · simp [beq_false_of_ne hcV]
          obtain ⟨midCli, hmid_lkp, hmid_eq⟩ := parseShortBundle_boolPrefix_append hprops heff
            rootSpec.name st.subPath validators st.cliOpts pcs pnames [oc] hpre
          have hsb_oc : Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp
              st.curSpec.shortVersion rootSpec.name st.subPath st.effectiveVersion st.curSpec validators
              midCli [oc] = .ok (midCli, some o) := by
            unfold Internal.parseShortBundle
            simp [hnh, hnV, hf, hkb_f]
          obtain ⟨c0, tailCs, hfull_cs, hc0_ne⟩ :
              ∃ c0 tailCs, pcs ++ [oc] = c0 :: tailCs ∧ c0 ≠ '-' := by
            cases hpcs : pcs with
            | nil => exact ⟨oc, [], rfl, hoc_ne⟩
            | cons c rest => exact ⟨c, rest ++ [oc], rfl, shortPrefix_head_ne_dash hprops.validOpts hpre hpcs⟩
          let tok1 := String.ofList ('-' :: (pcs ++ [oc]))
          have htok_list : tok1.toList = '-' :: c0 :: tailCs := by
            dsimp only [tok1]; rw [String.toList_ofList, hfull_cs]
          have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList tok1
            (fun heq => by rw [htok_list] at heq; exact hc0_ne (List.cons.inj (List.cons.inj heq).2).1)
            (fun heq => by rw [htok_list] at heq; exact hc0_ne (List.cons.inj (List.cons.inj heq).2).1)
            (fun heq => by rw [htok_list] at heq; exact hc0_ne (List.cons.inj (List.cons.inj heq).2).1)
          have hstep1 : Internal.stepToken rootSpec.name validators st tok1 =
              .ok { st with cliOpts := midCli, pendingOpt := some o } := by
            unfold Internal.stepToken
            simp only [hp_none, had_false, beq_false_of_ne hne_dd, beq_false_of_ne hne_help,
              beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            rw [htok_list]
            split
            · rename_i _ heq; exact absurd (List.cons.inj (List.cons.inj heq).2).1 hc0_ne
            · rename_i _ c' sr' _ heq
              have hc' := (List.cons.inj (List.cons.inj heq).2).1
              have hsr' := (List.cons.inj (List.cons.inj heq).2).2
              subst hc' hsr'
              rw [← hfull_cs, hmid_eq, hsb_oc]; rfl
            · rename_i _ _ h2; exact absurd rfl (h2 c0 tailCs)
          have hstep2 : Internal.stepToken rootSpec.name validators { st with cliOpts := midCli, pendingOpt := some o } rv =
              .ok { st with cliOpts := Internal.recordCliOpt midCli o.name val, pendingOpt := none } := by
            unfold Internal.stepToken
            simp [parseOptValueWithFast_eq, hpv, Bind.bind, Except.bind]
          refine ⟨{ st with cliOpts := Internal.recordCliOpt midCli o.name val, pendingOpt := none }, ?_,
            rfl, rfl, rfl, by simp [Model.CliPhrase.subcmd?], rfl, had_false,
            by simp [Model.CliPhrase.posTokens], rfl, fun k => ?_⟩
          · dsimp only [tok1] at hstep1
            unfold Model.CliPhrase.tokens Internal.parseTokensLoop
            rw [hstep1]; dsimp only [Bind.bind, Except.bind]
            unfold Internal.parseTokensLoop
            rw [hstep2]; rfl
          · rw [recordCliOpt_rev_eq, hmid_lkp k, hname_eq, Model.CliPhrase.optEvents,
              eventsForOpt_append, List.append_assoc]
  | positional tok =>
    unfold Model.validSinglePhraseStep at hstep
    dsimp only at hstep
    by_cases hok : (Model.isPlainCliTokenBool tok && (st.curSpec.subcommands.isEmpty || !st.rawPositionals.isEmpty)) = true
    rotate_left; · simp [hok] at hstep
    simp only [hok, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hstep
    rcases hstep with ⟨rfl, rfl, rfl, rfl, rfl⟩
    rw [Bool.and_eq_true] at hok
    rcases hok with ⟨hplain, hleaf_or_seen⟩
    have hnot_dash2 : ∀ c rest, tok.toList ≠ '-' :: c :: rest := by
      intro c rest heq
      unfold Model.isPlainCliTokenBool at hplain
      rw [heq] at hplain; cases hplain
    have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList tok
      (hnot_dash2 '-' [])
      (hnot_dash2 '-' ['h', 'e', 'l', 'p'])
      (hnot_dash2 '-' ['v', 'e', 'r', 's', 'i', 'o', 'n'])
    have hsc_f : (!st.curSpec.subcommands.isEmpty && st.rawPositionals.isEmpty) = false := by
      cases h1 : st.curSpec.subcommands.isEmpty <;> cases h2 : st.rawPositionals.isEmpty <;> simp_all
    refine ⟨{ st with rawPositionals := tok :: st.rawPositionals }, ?_,
      rfl, rfl, rfl, by simp [Model.CliPhrase.subcmd?], hp_none, had_false,
      by simp [Model.CliPhrase.posTokens], rfl,
      fun k => by simp [Model.CliPhrase.optEvents, eventsForOpt]⟩
    unfold Model.CliPhrase.tokens Internal.parseTokensLoop Internal.stepToken
    simp only [hp_none, had_false, beq_false_of_ne hne_dd, beq_false_of_ne hne_help,
      beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i longRest heq; exact absurd heq (hnot_dash2 '-' longRest)
    · rename_i c sr _ heq; exact absurd heq (hnot_dash2 c sr)
    · simp [hsc_f, Bind.bind, Except.bind, Internal.parseTokensLoop]
  | dashDashTail tail =>
    unfold Model.validSinglePhraseStep at hstep
    dsimp only at hstep
    simp only [Option.some.injEq, Prod.mk.injEq] at hstep
    rcases hstep with ⟨rfl, rfl, rfl, rfl, rfl⟩
    cases st with
    | mk curSpec subPath inheritedGlobals effectiveVersion afterDashDash pendingOpt cliOpts rawPositionals =>
      dsimp only at hp_none had_false ⊢
      subst hp_none had_false
      refine ⟨{ curSpec := curSpec, subPath := subPath, inheritedGlobals := inheritedGlobals,
                effectiveVersion := effectiveVersion, afterDashDash := true, pendingOpt := none,
                cliOpts := cliOpts, rawPositionals := tail.reverse ++ rawPositionals }, ?_,
        rfl, rfl, rfl, by simp [Model.CliPhrase.subcmd?], rfl, rfl,
        by simp [Model.CliPhrase.posTokens], ?_,
        fun k => by simp [Model.CliPhrase.optEvents, eventsForOpt]⟩
      · unfold Model.CliPhrase.tokens Internal.parseTokensLoop Internal.stepToken
        simp only [Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, Bind.bind, Except.bind]
        exact parseTokensLoop_afterDashDash rootSpec.name validators
          { curSpec := curSpec, subPath := subPath, inheritedGlobals := inheritedGlobals,
            effectiveVersion := effectiveVersion, afterDashDash := true, pendingOpt := none,
            cliOpts := cliOpts, rawPositionals := rawPositionals } tail rfl rfl
      · cases tail with
        | nil => simp
        | cons t ts =>
          cases ht : (t :: ts).reverse with
          | nil => have hlen := congrArg List.length ht; simp at hlen
          | cons _ _ => simp

/-- Soundness of `Model.checkCliPhrases` against `Internal.parseTokensLoop`. -/
theorem checkCliPhrases_sound {rootSpec : CommandSpec} {validators : CustomValidators}
    (st : Internal.ParseState) (phrases : List Model.CliPhrase)
    (hinv : ParseStateInv rootSpec st) (hp_none : st.pendingOpt = none)
    (had_false : st.afterDashDash = false)
    (hchk : Model.checkCliPhrases validators st.inheritedGlobals st.effectiveVersion
      st.curSpec (!st.rawPositionals.isEmpty) phrases = true) :
    ∃ finalSt : Internal.ParseState,
      Internal.parseTokensLoop rootSpec.name validators st ((phrases.map Model.CliPhrase.tokens).flatten) =
        .ok finalSt ∧
      finalSt.pendingOpt = none ∧
      finalSt.subPath = st.subPath ++ phrases.filterMap Model.CliPhrase.subcmd? ∧
      finalSt.rawPositionals = (phrases.flatMap Model.CliPhrase.posTokens).reverse ++ st.rawPositionals ∧
      (∀ k, (lookupCli finalSt.cliOpts k).reverse =
        (lookupCli st.cliOpts k).reverse ++ eventsForOpt (phrases.flatMap Model.CliPhrase.optEvents) k) := by
  induction phrases generalizing st with
  | nil =>
    refine ⟨st, rfl, hp_none, by simp, by simp, fun k => by simp [eventsForOpt]⟩
  | cons p rest ih =>
    unfold Model.checkCliPhrases at hchk
    cases hstep : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
        st.curSpec (!st.rawPositionals.isEmpty) p with
    | none => rw [hstep] at hchk; cases hchk
    | some nextTuple =>
      rcases nextTuple with ⟨nextG, nextVer, nextSpec, nextSeenPos, mustEnd⟩
      rw [hstep] at hchk; dsimp only at hchk
      obtain ⟨st1, hloop1, hspec1, hg1, hver1, hsub1, hp1, had1, hpos1, hseen1, hcli1⟩ :=
        singlePhrase_sound hinv hp_none had_false hstep
      have hinv1 : ParseStateInv rootSpec st1 := parseTokensLoop_sound rootSpec st hinv p.tokens hloop1
      by_cases hme : mustEnd = true
      · simp only [hme, ↓reduceIte, List.isEmpty_iff] at hchk
        subst hchk
        refine ⟨st1, ?_, hp1, ?_, ?_, ?_⟩
        · simpa [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] using hloop1
        · rw [hsub1, List.filterMap_cons, List.filterMap_nil]
          cases p.subcmd? <;> simp
        · simpa [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hpos1
        · intro k; simpa [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hcli1 k
      · simp only [hme, Bool.false_eq_true, ↓reduceIte] at hchk
        have had1_f : st1.afterDashDash = false := by rw [had1]; exact Bool.eq_false_iff.mpr hme
        rw [← hg1, ← hver1, ← hspec1, ← hseen1] at hchk
        obtain ⟨finalSt, hloop2, hpf, hsubf, hposf, hclif⟩ := ih st1 hinv1 hp1 had1_f hchk
        refine ⟨finalSt, ?_, hpf, ?_, ?_, ?_⟩
        · simp only [List.map_cons, List.flatten_cons]
          rw [parseTokensLoop_append rootSpec.name validators p.tokens _ st st1 hloop1]
          exact hloop2
        · rw [hsubf, hsub1, List.filterMap_cons, List.append_assoc]
          cases p.subcmd? <;> simp
        · rw [hposf, hpos1, List.flatMap_cons, List.reverse_append, List.append_assoc]
        · intro k
          rw [hclif k, hcli1 k, List.flatMap_cons, eventsForOpt_append, List.append_assoc]

/-- Soundness of `Model.runOpenCliPhrases` against `Internal.parseTokensLoop`. -/
theorem runOpenCliPhrases_sound {rootSpec : CommandSpec} {validators : CustomValidators}
    (st : Internal.ParseState) (phrases : List Model.CliPhrase)
    {globals : List OptSpec} {effVer : Option String} {curSpec : CommandSpec} {seenPos : Bool}
    (hinv : ParseStateInv rootSpec st) (hp_none : st.pendingOpt = none)
    (had_false : st.afterDashDash = false)
    (hrun : Model.runOpenCliPhrases validators st.inheritedGlobals st.effectiveVersion
      st.curSpec (!st.rawPositionals.isEmpty) phrases = some (globals, effVer, curSpec, seenPos)) :
    ∃ nextSt : Internal.ParseState,
      Internal.parseTokensLoop rootSpec.name validators st ((phrases.map Model.CliPhrase.tokens).flatten) =
        .ok nextSt ∧
      ParseStateInv rootSpec nextSt ∧
      nextSt.pendingOpt = none ∧
      nextSt.afterDashDash = false ∧
      nextSt.inheritedGlobals = globals ∧
      nextSt.effectiveVersion = effVer ∧
      nextSt.curSpec = curSpec := by
  induction phrases generalizing st with
  | nil =>
    unfold Model.runOpenCliPhrases at hrun
    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl, rfl, rfl, _⟩
    exact ⟨st, rfl, hinv, hp_none, had_false, rfl, rfl, rfl⟩
  | cons p rest ih =>
    unfold Model.runOpenCliPhrases at hrun
    cases hstep : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
        st.curSpec (!st.rawPositionals.isEmpty) p with
    | none => rw [hstep] at hrun; cases hrun
    | some nextTuple =>
      rcases nextTuple with ⟨nextG, nextVer, nextSpec, nextSeenPos, mustEnd⟩
      rw [hstep] at hrun; dsimp only at hrun
      by_cases hme : mustEnd = true
      · simp [hme] at hrun
      · simp only [hme, Bool.false_eq_true, ↓reduceIte] at hrun
        obtain ⟨st1, hloop1, hspec1, hg1, hver1, _, hp1, had1, _, hseen1, _⟩ :=
          singlePhrase_sound hinv hp_none had_false hstep
        have had1_f : st1.afterDashDash = false := by rw [had1]; exact Bool.eq_false_iff.mpr hme
        have hinv1 := parseTokensLoop_sound rootSpec st hinv p.tokens hloop1
        rw [← hg1, ← hver1, ← hspec1, ← hseen1] at hrun
        obtain ⟨finalSt, hloop2, hinvf, hpf, hadf, hgf, hverf, hspecf⟩ :=
          ih st1 hinv1 hp1 had1_f hrun
        refine ⟨finalSt, ?_, hinvf, hpf, hadf, hgf, hverf, hspecf⟩
        simp only [List.map_cons, List.flatten_cons]
        rw [parseTokensLoop_append rootSpec.name validators p.tokens _ st st1 hloop1]
        exact hloop2

private theorem shortPrefix_help_sound {vp : Option String}
    {curSpec : CommandSpec} {globals : List OptSpec} {effVer : Option String}
    (hprops : NodeProps curSpec globals vp)
    (heff : effVer = (curSpec.version <|> vp))
    (hsh : curSpec.shortHelp = true)
    (rootName : String) (subPath : List String) (validators : CustomValidators)
    (cliOpts : List (String × List OptValue)) (cs : List Char)
    (hhas : Model.hasShortPrefixBeforeCharBool (globals ++ curSpec.options) 'h' cs = true) :
    ∃ e : CmdLineError,
      Internal.parseShortBundle (globals ++ curSpec.options) curSpec.shortHelp curSpec.shortVersion
        rootName subPath effVer curSpec validators cliOpts cs = .error e ∧
      e.kind = .helpRequested ∧ (!e.message.isEmpty) = true := by
  induction cs generalizing cliOpts with
  | nil => simp [Model.hasShortPrefixBeforeCharBool] at hhas
  | cons ch rest ih =>
    unfold Model.hasShortPrefixBeforeCharBool at hhas
    by_cases hch : ch = 'h'
    · subst hch
      unfold Internal.parseShortBundle
      simp only [beq_self_eq_true, hsh, Bool.and_self, ↓reduceIte]
      exact ⟨{ kind := .helpRequested,
               message := Internal.renderHelpNode (rootName :: subPath) (globals ++ curSpec.options) effVer curSpec },
        rfl, rfl, renderHelpNode_nonEmpty_shared (rootName :: subPath) (globals ++ curSpec.options) effVer curSpec⟩
    · simp only [beq_false_of_ne hch, Bool.false_eq_true, ↓reduceIte] at hhas
      cases hf : (globals ++ curSpec.options).find? (fun o => o.short == some ch) with
      | none => rw [hf] at hhas; cases hhas
      | some o =>
        rw [hf] at hhas; rw [Bool.and_eq_true] at hhas
        have ho := List.mem_of_find?_eq_some hf
        have hs := beq_iff_eq.mp (List.find?_some (p := fun (x : OptSpec) => x.short == some ch) hf)
        have hch_mem : ch ∈ (globals ++ curSpec.options).filterMap (·.short) :=
          List.mem_filterMap.mpr ⟨o, ho, hs⟩
        have hnV : (ch == 'V' && curSpec.shortVersion && effVer.isSome) = false := by
          rw [heff]
          cases hsv : (curSpec.shortVersion && (curSpec.version <|> vp).isSome)
          · cases h1 : curSpec.shortVersion <;> cases h2 : (curSpec.version <|> vp).isSome <;> simp_all
          · by_cases hcV : ch = 'V'
            · subst hcV; exact absurd hch_mem (hprops.noShortVer hsv)
            · simp [beq_false_of_ne hcV]
        unfold Internal.parseShortBundle
        simp only [beq_false_of_ne hch, Bool.false_and, hnV, hf, hhas.1, Bool.false_eq_true, ↓reduceIte]
        exact ih _ hhas.2

private theorem shortPrefix_version_sound {vp : Option String}
    {curSpec : CommandSpec} {globals : List OptSpec} {effVer : Option String}
    (hprops : NodeProps curSpec globals vp)
    (hsv : curSpec.shortVersion = true) (hver_some : effVer.isSome = true)
    (rootName : String) (subPath : List String) (validators : CustomValidators)
    (cliOpts : List (String × List OptValue)) (cs : List Char)
    (hhas : Model.hasShortPrefixBeforeCharBool (globals ++ curSpec.options) 'V' cs = true) :
    ∃ e : CmdLineError,
      Internal.parseShortBundle (globals ++ curSpec.options) curSpec.shortHelp curSpec.shortVersion
        rootName subPath effVer curSpec validators cliOpts cs = .error e ∧
      e.kind = .versionRequested ∧ (!e.message.isEmpty) = true := by
  induction cs generalizing cliOpts with
  | nil => simp [Model.hasShortPrefixBeforeCharBool] at hhas
  | cons ch rest ih =>
    unfold Model.hasShortPrefixBeforeCharBool at hhas
    by_cases hch : ch = 'V'
    · subst hch
      unfold Internal.parseShortBundle
      have hnh : (('V' == 'h') && curSpec.shortHelp) = false := rfl
      cases hev : effVer with
      | none => simp [hev] at hver_some
      | some v =>
        simp only [hnh, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, hsv,
          Option.isSome_some, Bool.and_self]
        exact ⟨{ kind := .versionRequested, message := Internal.renderVersion rootName v },
          rfl, rfl, renderVersion_nonEmpty rootName v⟩
    · simp only [beq_false_of_ne hch, Bool.false_eq_true, ↓reduceIte] at hhas
      cases hf : (globals ++ curSpec.options).find? (fun o => o.short == some ch) with
      | none => rw [hf] at hhas; cases hhas
      | some o =>
        rw [hf] at hhas; rw [Bool.and_eq_true] at hhas
        have ho := List.mem_of_find?_eq_some hf
        have hs := beq_iff_eq.mp (List.find?_some (p := fun (x : OptSpec) => x.short == some ch) hf)
        have hch_mem : ch ∈ (globals ++ curSpec.options).filterMap (·.short) :=
          List.mem_filterMap.mpr ⟨o, ho, hs⟩
        have hnh : (ch == 'h' && curSpec.shortHelp) = false := by
          cases hsh : curSpec.shortHelp
          · simp
          · by_cases hchh : ch = 'h'
            · subst hchh; exact absurd hch_mem (hprops.noShortHelp hsh)
            · simp [beq_false_of_ne hchh]
        unfold Internal.parseShortBundle
        simp only [hnh, beq_false_of_ne hch, Bool.false_and, hf, hhas.1, Bool.false_eq_true, ↓reduceIte]
        exact ih _ hhas.2

private theorem initParseStateInv {spec : CommandSpec} (hv : Model.isValidSpec spec = true) :
    ParseStateInv spec { curSpec := spec, effectiveVersion := spec.version } :=
  ⟨⟨none, ⟨hv, rfl⟩, by cases spec.version <;> rfl⟩,
    by unfold Model.findSubcommandPath Model.findSubcommandPath.go; dsimp only; cases spec.version <;> rfl,
    ⟨fun _ h => absurd rfl h, fun _ _ _ h => by cases h⟩,
    fun _ h => by cases h⟩

/-- Soundness of `Model.ExistsHelpInvocation`: guarantees `.error e` with `e.kind = .helpRequested`. -/
theorem existsHelpInvocation_sound {spec : CommandSpec} {validators : CustomValidators}
    {args : List String} (hv : Model.isValidSpec spec = true)
    (hhelp : Model.ExistsHelpInvocation spec validators args) :
    ∃ e : CmdLineError,
      Internal.parseTokens spec.name validators { curSpec := spec, effectiveVersion := spec.version } args =
        .error e ∧
      e.kind = .helpRequested ∧ (!e.message.isEmpty) = true := by
  rcases hhelp with ⟨phrases, triggerTok, tail, globals, effVer, curSpec, seenPos, hrun, hargs, htrig⟩
  have hinv0 := initParseStateInv hv
  obtain ⟨st, hloop_pre, hinv_st, hp_none, had_false, hg_eq, hver_eq, hspec_eq⟩ :=
    runOpenCliPhrases_sound { curSpec := spec, effectiveVersion := spec.version } phrases hinv0 rfl rfl hrun
  subst hg_eq hver_eq hspec_eq hargs
  rcases hinv_st with ⟨⟨vp, hnode, heff⟩, _, _, _⟩
  have hprops := nodeInv_props hnode
  have htrig_step : ∃ e : CmdLineError,
      Internal.stepToken spec.name validators st triggerTok = .error e ∧
      e.kind = .helpRequested ∧ (!e.message.isEmpty) = true := by
    unfold Model.isHelpTriggerTokenBool at htrig
    by_cases hhh : (triggerTok == "--help") = true
    · have hndd : (triggerTok == "--") = false := by
        rw [beq_iff_eq.mp hhh]; rfl
      unfold Internal.stepToken
      simp only [hp_none, had_false, hndd, hhh, Bool.false_eq_true, ↓reduceIte]
      exact ⟨{ kind := .helpRequested,
               message := Internal.renderHelpNode (spec.name :: st.subPath)
                 (st.inheritedGlobals ++ st.curSpec.options) st.effectiveVersion st.curSpec },
        rfl, rfl, renderHelpNode_nonEmpty_shared (spec.name :: st.subPath)
          (st.inheritedGlobals ++ st.curSpec.options) st.effectiveVersion st.curSpec⟩
    · simp only [hhh, Bool.false_or, Bool.and_eq_true] at htrig
      rcases htrig with ⟨hsh, hshort⟩
      cases htl : triggerTok.toList with
      | nil => simp [htl] at hshort
      | cons d rest0 =>
        by_cases hd : d = '-'
        · subst hd
          cases rest0 with
          | nil => simp [htl] at hshort
          | cons c rest =>
            simp only [htl, Bool.and_eq_true] at hshort
            have hc_ne : c ≠ '-' := by
              intro hce; subst hce; simp at hshort
            have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList triggerTok
              (fun heq => by rw [htl] at heq; exact hc_ne (List.cons.inj (List.cons.inj heq).2).1)
              (fun heq => by rw [htl] at heq; exact hc_ne (List.cons.inj (List.cons.inj heq).2).1)
              (fun heq => by rw [htl] at heq; exact hc_ne (List.cons.inj (List.cons.inj heq).2).1)
            obtain ⟨e, hsb, hk, hm⟩ := shortPrefix_help_sound hprops heff hsh
              spec.name st.subPath validators st.cliOpts (c :: rest) hshort.2
            refine ⟨e, ?_, hk, hm⟩
            unfold Internal.stepToken
            simp only [hp_none, had_false, beq_false_of_ne hne_dd, beq_false_of_ne hne_help,
              beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            rw [htl]
            split
            · rename_i _ heq; exact absurd (List.cons.inj (List.cons.inj heq).2).1 hc_ne
            · rename_i _ c' sr' _ heq
              have hc' := (List.cons.inj (List.cons.inj heq).2).1
              have hsr' := (List.cons.inj (List.cons.inj heq).2).2
              subst hc' hsr'; simp [hsb, Bind.bind, Except.bind]
            · rename_i _ _ h2; exact absurd rfl (h2 c rest)
        · cases rest0 with
          | nil => simp [htl] at hshort
          | cons _ _ =>
            rw [htl] at hshort
            split at hshort
            · rename_i _ _ heq; exact absurd (List.cons.inj heq).1 hd
            · cases hshort
  obtain ⟨e, hst_err, hk, hm⟩ := htrig_step
  refine ⟨e, ?_, hk, hm⟩
  unfold Internal.parseTokens
  rw [parseTokensLoop_append spec.name validators _ _ _ st hloop_pre]
  unfold Internal.parseTokensLoop
  simp [hst_err, Bind.bind, Except.bind]

/-- Soundness of `Model.ExistsVersionInvocation`: guarantees `.error e` with `e.kind = .versionRequested`. -/
theorem existsVersionInvocation_sound {spec : CommandSpec} {validators : CustomValidators}
    {args : List String} (hv : Model.isValidSpec spec = true)
    (hver : Model.ExistsVersionInvocation spec validators args) :
    ∃ e : CmdLineError,
      Internal.parseTokens spec.name validators { curSpec := spec, effectiveVersion := spec.version } args =
        .error e ∧
      e.kind = .versionRequested ∧ (!e.message.isEmpty) = true := by
  rcases hver with ⟨phrases, triggerTok, tail, globals, effVer, curSpec, seenPos, hrun, hargs, htrig⟩
  have hinv0 := initParseStateInv hv
  obtain ⟨st, hloop_pre, hinv_st, hp_none, had_false, hg_eq, hver_eq, hspec_eq⟩ :=
    runOpenCliPhrases_sound { curSpec := spec, effectiveVersion := spec.version } phrases hinv0 rfl rfl hrun
  subst hg_eq hver_eq hspec_eq hargs
  rcases hinv_st with ⟨⟨_, hnode, _⟩, _, _, _⟩
  have hprops := nodeInv_props hnode
  have htrig_step : ∃ e : CmdLineError,
      Internal.stepToken spec.name validators st triggerTok = .error e ∧
      e.kind = .versionRequested ∧ (!e.message.isEmpty) = true := by
    unfold Model.isVersionTriggerTokenBool at htrig
    rw [Bool.and_eq_true] at htrig
    rcases htrig with ⟨hev_some, hrest_trig⟩
    by_cases hvv : (triggerTok == "--version") = true
    · have hndd : (triggerTok == "--") = false := by rw [beq_iff_eq.mp hvv]; rfl
      have hnhelp : (triggerTok == "--help") = false := by rw [beq_iff_eq.mp hvv]; rfl
      cases hev : st.effectiveVersion with
      | none => simp [hev] at hev_some
      | some v =>
        unfold Internal.stepToken
        simp only [hp_none, had_false, hndd, hnhelp, hvv, hev, Option.isSome_some,
          Bool.and_self, Bool.false_eq_true, ↓reduceIte]
        exact ⟨{ kind := .versionRequested, message := Internal.renderVersion spec.name v },
          rfl, rfl, renderVersion_nonEmpty spec.name v⟩
    · simp only [hvv, Bool.false_or, Bool.and_eq_true] at hrest_trig
      rcases hrest_trig with ⟨hsv, hshort⟩
      cases htl : triggerTok.toList with
      | nil => simp [htl] at hshort
      | cons d rest0 =>
        by_cases hd : d = '-'
        · subst hd
          cases rest0 with
          | nil => simp [htl] at hshort
          | cons c rest =>
            simp only [htl, Bool.and_eq_true] at hshort
            have hc_ne : c ≠ '-' := by intro hce; subst hce; simp at hshort
            have ⟨hne_dd, hne_help, hne_ver⟩ := ne_special_of_toList triggerTok
              (fun heq => by rw [htl] at heq; exact hc_ne (List.cons.inj (List.cons.inj heq).2).1)
              (fun heq => by rw [htl] at heq; exact hc_ne (List.cons.inj (List.cons.inj heq).2).1)
              (fun heq => by rw [htl] at heq; exact hc_ne (List.cons.inj (List.cons.inj heq).2).1)
            obtain ⟨e, hsb, hk, hm⟩ := shortPrefix_version_sound hprops hsv hev_some
              spec.name st.subPath validators st.cliOpts (c :: rest) hshort.2
            refine ⟨e, ?_, hk, hm⟩
            unfold Internal.stepToken
            simp only [hp_none, had_false, beq_false_of_ne hne_dd, beq_false_of_ne hne_help,
              beq_false_of_ne hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            rw [htl]
            split
            · rename_i _ heq; exact absurd (List.cons.inj (List.cons.inj heq).2).1 hc_ne
            · rename_i _ c' sr' _ heq
              have hc' := (List.cons.inj (List.cons.inj heq).2).1
              have hsr' := (List.cons.inj (List.cons.inj heq).2).2
              subst hc' hsr'; simp [hsb, Bind.bind, Except.bind]
            · rename_i _ _ h2; exact absurd rfl (h2 c rest)
        · cases rest0 with
          | nil => simp [htl] at hshort
          | cons _ _ =>
            rw [htl] at hshort
            split at hshort
            · rename_i _ _ heq; exact absurd (List.cons.inj heq).1 hd
            · cases hshort
  obtain ⟨e, hst_err, hk, hm⟩ := htrig_step
  refine ⟨e, ?_, hk, hm⟩
  unfold Internal.parseTokens
  rw [parseTokensLoop_append spec.name validators _ _ _ st hloop_pre]
  unfold Internal.parseTokensLoop
  simp [hst_err, Bind.bind, Except.bind]

/-- Soundness of `Model.ValidParsedCmd`: guarantees `Internal.parseWithEnvSpecM` returns `.ok parsed`. -/
theorem validParsedCmd_sound {W : Type} {ops : CliOpsM (StateM W)}
    {getEnv : String → Except CmdLineError (Option String)} {w : W}
    {spec : CommandSpec} {args : List String} {validators : CustomValidators} {parsed : ParsedCmd}
    (hro_eq : ∀ visibleOpts cliOpts,
      (Internal.resolveOptionsTR ops.getEnv visibleOpts cliOpts validators w).1 =
        Model.resolveOptions (m := Id) getEnv visibleOpts cliOpts validators)
    (hv : Model.ValidParsedCmd getEnv spec args validators parsed) :
    (Internal.parseWithEnvSpecM ops spec args validators w).1 = .ok parsed := by
  rcases hv with ⟨hspec_ok, globals, effVer, targetSpec, hpath_ok, hleaf,
    phrases, hargs_eq, hchk_ok, hsub_eq, hpos_eq, hres_opts, hres_args⟩
  have hinv0 := initParseStateInv hspec_ok
  obtain ⟨loopSt, hloop, hp_none, hsub_st, hpos_st, hcli_st⟩ :=
    checkCliPhrases_sound { curSpec := spec, effectiveVersion := spec.version } phrases hinv0 rfl rfl hchk_ok
  simp only [List.nil_append, List.append_nil] at hsub_st hpos_st
  have hpt : Internal.parseTokens spec.name validators { curSpec := spec, effectiveVersion := spec.version } args =
      .ok { loopSt with
            cliOpts := loopSt.cliOpts.map (fun p => (p.1, p.2.reverse)),
            rawPositionals := loopSt.rawPositionals.reverse } := by
    rw [← hargs_eq]
    unfold Internal.parseTokens
    simp [hloop, hp_none, Bind.bind, Except.bind]
  have ⟨hinv_final, _⟩ := parseTokens_sound spec { curSpec := spec, effectiveVersion := spec.version } hinv0 args hpt
  rcases hinv_final with ⟨⟨vp_f, hnode_f, _⟩, hpath_f, _, _⟩
  dsimp only at hnode_f hpath_f
  rw [hsub_st, hsub_eq, hpath_ok] at hpath_f
  injection hpath_f with htriple
  rcases Prod.mk.inj htriple with ⟨hg_f, htriple⟩
  rcases Prod.mk.inj htriple with ⟨_, hspec_f⟩
  subst hg_f hspec_f
  have hprops_f := nodeInv_props hnode_f
  have hlkp_eq : ∀ opt ∈ loopSt.inheritedGlobals ++ loopSt.curSpec.options,
      lookupCli (loopSt.cliOpts.map (fun p => (p.1, p.2.reverse))) opt.name =
        lookupCli (Model.cliOptsOfPhrases (loopSt.inheritedGlobals ++ loopSt.curSpec.options) phrases) opt.name := by
    intro opt ho
    have hinit_cli : (lookupCli ({ curSpec := spec, effectiveVersion := spec.version } : Internal.ParseState).cliOpts opt.name).reverse = [] := rfl
    rw [lookupCli_map_rev, hcli_st opt.name, hinit_cli, List.nil_append, lookupCli_cliOptsOfPhrases hprops_f.nodupNames phrases ho]
  unfold Internal.parseWithEnvSpecM
  rw [isValidSpecTR_eq, hspec_ok]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpt, hleaf, Bind.bind, StateT.bind]
  have hro_val := hro_eq (loopSt.inheritedGlobals ++ loopSt.curSpec.options)
    (loopSt.cliOpts.map (fun p => (p.1, p.2.reverse)))
  rw [resolveOptions_congr_lookup hlkp_eq, hres_opts] at hro_val
  cases hRunRo : Internal.resolveOptionsTR ops.getEnv (loopSt.inheritedGlobals ++ loopSt.curSpec.options)
      (loopSt.cliOpts.map (fun p => (p.1, p.2.reverse))) validators w with
  | mk roRes w1 =>
    rw [hRunRo] at hro_val; dsimp only at hro_val
    subst hro_val
    dsimp only
    rw [resolveArgsTR_eq, hpos_st, List.reverse_reverse, hres_args]
    simp only [Pure.pure, StateT.pure]
    cases parsed
    dsimp only at hsub_eq hpos_eq ⊢
    rw [hsub_st, hsub_eq, hpos_eq]

private def OtherErrKind (k : CmdLineErrorKind) : Prop :=
  k ≠ .invalidSpec ∧ k ≠ .helpRequested ∧ k ≠ .versionRequested ∧ k ≠ .eof ∧ k ≠ .ioError

private theorem otherErrKind_unknownOption : OtherErrKind .unknownOption := by
  unfold OtherErrKind; decide

private theorem otherErrKind_unknownSubcommand : OtherErrKind .unknownSubcommand := by
  unfold OtherErrKind; decide

private theorem otherErrKind_missingOption : OtherErrKind .missingOption := by
  unfold OtherErrKind; decide

private theorem otherErrKind_missingArgument : OtherErrKind .missingArgument := by
  unfold OtherErrKind; decide

private theorem otherErrKind_unexpectedArgument : OtherErrKind .unexpectedArgument := by
  unfold OtherErrKind; decide

private theorem otherErrKind_invalidValue : OtherErrKind .invalidValue := by
  unfold OtherErrKind; decide

private theorem resolveOptDefault_err_props {opt : OptSpec} {validators : CustomValidators}
    {e : CmdLineError} (h : Model.resolveOptDefault opt validators = .error e) :
    (!e.message.isEmpty) = true ∧ OtherErrKind e.kind := by
  unfold Model.resolveOptDefault at h
  cases hd : opt.default with
  | some d =>
    rw [hd] at h; dsimp only at h
    cases hp : Model.parseOptValueWith opt.kind d validators with
    | ok _ => rw [hp] at h; cases h
    | error e0 =>
      rw [hp] at h; injection h with he; subst he
      obtain ⟨hm, hk⟩ := parseOptValueWith_err_props hp
      exact ⟨hm, hk ▸ otherErrKind_invalidValue⟩
  | none =>
    rw [hd] at h; dsimp only at h
    cases hreq : opt.required with
    | true =>
      rw [hreq] at h; simp only [↓reduceIte] at h
      injection h with he; subst he
      exact ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), otherErrKind_missingOption⟩
    | false =>
      rw [hreq] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      split at h <;> cases h

private theorem resolveSingleOption_err_props {getEnv : String → Except CmdLineError (Option String)}
    {opt : OptSpec} {cliVals : List OptValue} {validators : CustomValidators} {e : CmdLineError}
    (h : Model.resolveSingleOption (m := Id) getEnv opt cliVals validators = .error e) :
    (∃ envKey : String, getEnv envKey = .error e) ∨ ((!e.message.isEmpty) = true ∧ OtherErrKind e.kind) := by
  unfold Model.resolveSingleOption at h
  dsimp only [Bind.bind, Pure.pure, Id.instMonad] at h
  cases hne : (!cliVals.isEmpty) with
  | true =>
    rw [hne] at h; simp only [↓reduceIte] at h
    cases hdup : (!opt.repeatable && decide (cliVals.length > 1)) with
    | false => rw [hdup] at h; cases h
    | true =>
      rw [hdup] at h; simp only [↓reduceIte] at h
      injection h with he; subst he
      exact Or.inr ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), otherErrKind_invalidValue⟩
  | false =>
    rw [hne] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases henv : opt.envVar with
    | none => rw [henv] at h; exact Or.inr (resolveOptDefault_err_props h)
    | some envKey =>
      rw [henv] at h; dsimp only at h
      cases hge : getEnv envKey with
      | error e0 =>
        rw [hge] at h; dsimp only at h; injection h with he; subst he
        exact Or.inl ⟨envKey, hge⟩
      | ok val? =>
        rw [hge] at h
        cases val? with
        | none => exact Or.inr (resolveOptDefault_err_props h)
        | some s =>
          if hs : s = "" then
            subst hs; exact Or.inr (resolveOptDefault_err_props h)
          else
            unfold Model.resolveSingleOption.match_1 at h
            simp only [hs, ↓reduceDIte] at h
            cases hp : Model.parseOptValueWith opt.kind s validators with
            | error e0 =>
              rw [hp] at h; dsimp only at h; injection h with he; subst he
              obtain ⟨hm, hk⟩ := parseOptValueWith_err_props hp
              exact Or.inr ⟨hm, hk ▸ otherErrKind_invalidValue⟩
            | ok v =>
              rw [hp] at h; dsimp only at h
              cases hc : (opt.repeatable && opt.kind == .bool && v == .bool false) <;>
                simp [hc] at h

private theorem resolveOptions_err_props {getEnv : String → Except CmdLineError (Option String)}
    {visibleOpts : List OptSpec} {cliOpts : List (String × List OptValue)}
    {validators : CustomValidators} {e : CmdLineError}
    (h : Model.resolveOptions (m := Id) getEnv visibleOpts cliOpts validators = .error e) :
    (∃ envKey : String, getEnv envKey = .error e) ∨ ((!e.message.isEmpty) = true ∧ OtherErrKind e.kind) := by
  induction visibleOpts with
  | nil => cases h
  | cons opt rest ih =>
    unfold Model.resolveOptions at h
    change (match Model.resolveSingleOption (m := Id) getEnv opt (lookupCli cliOpts opt.name) validators with
      | Except.error e0 => Except.error e0
      | Except.ok resolved? =>
        match Model.resolveOptions (m := Id) getEnv rest cliOpts validators with
        | Except.error e0 => Except.error e0
        | Except.ok tail => match resolved? with | none => Except.ok tail | some vals => Except.ok ((opt.name, vals) :: tail)) = Except.error e at h
    cases hs : Model.resolveSingleOption (m := Id) getEnv opt (lookupCli cliOpts opt.name) validators with
    | error e0 =>
      rw [hs] at h; injection h with he; subst he
      exact resolveSingleOption_err_props hs
    | ok res? =>
      rw [hs] at h; dsimp only at h
      cases htl : Model.resolveOptions (m := Id) getEnv rest cliOpts validators with
      | error e0 =>
        rw [htl] at h; injection h with he; subst he
        exact ih htl
      | ok tail =>
        rw [htl] at h; dsimp only at h
        cases res? <;> cases h

private theorem resolveArgs_parseMany_err_props {validators : CustomValidators}
    {arg : ArgSpec} {ss : List String} {e : CmdLineError}
    (h : Model.resolveArgs.parseMany validators arg ss = .error e) :
    (!e.message.isEmpty) = true ∧ OtherErrKind e.kind := by
  induction ss with
  | nil => cases h
  | cons s rest ih =>
    unfold Model.resolveArgs.parseMany at h
    dsimp only [Bind.bind, Except.bind] at h
    cases hp : Model.parseOptValueWith arg.kind s validators with
    | error e0 =>
      rw [hp] at h; dsimp only at h; injection h with he; subst he
      obtain ⟨hm, hk⟩ := parseOptValueWith_err_props hp
      exact ⟨hm, hk ▸ otherErrKind_invalidValue⟩
    | ok v =>
      rw [hp] at h; dsimp only at h
      cases hm : Model.resolveArgs.parseMany validators arg rest with
      | error e0 => rw [hm] at h; injection h with he; subst he; exact ih hm
      | ok _ => rw [hm] at h; cases h

private theorem resolveArgs_err_props {argSpecs : List ArgSpec} {rawPos : List String}
    {validators : CustomValidators} {e : CmdLineError}
    (h : Model.resolveArgs argSpecs rawPos validators = .error e) :
    (!e.message.isEmpty) = true ∧ OtherErrKind e.kind := by
  unfold Model.resolveArgs at h
  induction argSpecs generalizing rawPos with
  | nil =>
    cases rawPos with
    | nil => cases h
    | cons extra _ =>
      unfold Model.resolveArgs.go at h
      injection h with he; subst he
      exact ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), otherErrKind_unexpectedArgument⟩
  | cons arg rest ih =>
    unfold Model.resolveArgs.go at h
    cases hvar : arg.variadic with
    | true =>
      rw [hvar] at h; simp only [↓reduceIte, Bind.bind, Except.bind] at h
      cases hemp : rawPos.isEmpty with
      | true =>
        rw [hemp] at h; simp only [↓reduceIte] at h
        cases hreq : arg.required with
        | true =>
          rw [hreq] at h; simp only [↓reduceIte] at h
          injection h with he; subst he
          exact ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), otherErrKind_missingArgument⟩
        | false =>
          rw [hreq] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
          cases hd : arg.default with
          | none => rw [hd] at h; exact ih h
          | some d =>
            rw [hd] at h; dsimp only at h
            cases hp : Model.parseOptValueWith arg.kind d validators with
            | error e0 =>
              rw [hp] at h; dsimp only at h; injection h with he; subst he
              obtain ⟨hm, hk⟩ := parseOptValueWith_err_props hp
              exact ⟨hm, hk ▸ otherErrKind_invalidValue⟩
            | ok _ =>
              rw [hp] at h; dsimp only at h
              cases hg : Model.resolveArgs.go validators rest [] with
              | error e0 => rw [hg] at h; injection h with he; subst he; exact ih hg
              | ok _ => rw [hg] at h; cases h
      | false =>
        rw [hemp] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases hpm : Model.resolveArgs.parseMany validators arg rawPos with
        | error e0 =>
          rw [hpm] at h; injection h with he; subst he
          exact resolveArgs_parseMany_err_props hpm
        | ok _ =>
          rw [hpm] at h; dsimp only at h
          cases hg : Model.resolveArgs.go validators rest [] with
          | error e0 => rw [hg] at h; injection h with he; subst he; exact ih hg
          | ok _ => rw [hg] at h; cases h
    | false =>
      rw [hvar] at h; simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind] at h
      cases rawPos with
      | cons s remPos =>
        dsimp only at h
        cases hp : Model.parseOptValueWith arg.kind s validators with
        | error e0 =>
          rw [hp] at h; dsimp only at h; injection h with he; subst he
          obtain ⟨hm, hk⟩ := parseOptValueWith_err_props hp
          exact ⟨hm, hk ▸ otherErrKind_invalidValue⟩
        | ok _ =>
          rw [hp] at h; dsimp only at h
          cases hg : Model.resolveArgs.go validators rest remPos with
          | error e0 => rw [hg] at h; injection h with he; subst he; exact ih hg
          | ok _ => rw [hg] at h; cases h
      | nil =>
        dsimp only at h
        cases hreq : arg.required with
        | true =>
          rw [hreq] at h; simp only [↓reduceIte] at h
          injection h with he; subst he
          exact ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), otherErrKind_missingArgument⟩
        | false =>
          rw [hreq] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
          cases hd : arg.default with
          | none => rw [hd] at h; exact ih h
          | some d =>
            rw [hd] at h; dsimp only at h
            cases hp : Model.parseOptValueWith arg.kind d validators with
            | error e0 =>
              rw [hp] at h; dsimp only at h; injection h with he; subst he
              obtain ⟨hm, hk⟩ := parseOptValueWith_err_props hp
              exact ⟨hm, hk ▸ otherErrKind_invalidValue⟩
            | ok _ =>
              rw [hp] at h; dsimp only at h
              cases hg : Model.resolveArgs.go validators rest [] with
              | error e0 => rw [hg] at h; injection h with he; subst he; exact ih hg
              | ok _ => rw [hg] at h; cases h

private theorem parseShortBundle_err_classify (visibleOpts : List OptSpec)
    (shortHelp shortVersion : Bool) (rootName : String) (subPath : List String)
    (effVer : Option String) (curSpec : CommandSpec) (validators : CustomValidators)
    (cliOpts : List (String × List OptValue)) (cs : List Char) {e : CmdLineError}
    (h : Internal.parseShortBundle visibleOpts shortHelp shortVersion rootName subPath
      effVer curSpec validators cliOpts cs = .error e) :
    (e.kind = .helpRequested ∧ (!e.message.isEmpty) = true ∧
      shortHelp = true ∧ Model.hasShortPrefixBeforeCharBool visibleOpts 'h' cs = true) ∨
    (e.kind = .versionRequested ∧ (!e.message.isEmpty) = true ∧
      shortVersion = true ∧ effVer.isSome = true ∧
      Model.hasShortPrefixBeforeCharBool visibleOpts 'V' cs = true) ∨
    ((!e.message.isEmpty) = true ∧ OtherErrKind e.kind) := by
  induction cs generalizing cliOpts with
  | nil => cases h
  | cons c rest ih =>
    unfold Internal.parseShortBundle at h
    cases hh : (c == 'h' && shortHelp) with
    | true =>
      rw [hh] at h
      injection h with he; subst he
      rw [Bool.and_eq_true] at hh
      have hc : c = 'h' := beq_iff_eq.mp hh.1
      subst hc
      exact Or.inl ⟨rfl, renderHelpNode_nonEmpty_shared (rootName :: subPath) visibleOpts effVer curSpec,
        hh.2, by simp [Model.hasShortPrefixBeforeCharBool]⟩
    | false =>
      rw [hh] at h
      cases hv : (c == 'V' && shortVersion && effVer.isSome) with
      | true =>
        rw [hv] at h
        simp only [Bool.and_eq_true] at hv
        rcases hv with ⟨⟨hc_b, hsv⟩, hev_some⟩
        have hc : c = 'V' := beq_iff_eq.mp hc_b
        subst hc
        cases hev : effVer with
        | none => simp [hev] at hev_some
        | some v =>
          rw [hev] at h; dsimp only at h
          injection h with he; subst he
          exact Or.inr (Or.inl ⟨rfl, renderVersion_nonEmpty rootName v, hsv, rfl,
            by simp [Model.hasShortPrefixBeforeCharBool]⟩)
      | false =>
        rw [hv] at h
        cases hf : visibleOpts.find? (fun o => o.short == some c) with
        | none =>
          rw [hf] at h; dsimp only at h
          injection h with he; subst he
          exact Or.inr (Or.inr ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), otherErrKind_unknownOption⟩)
        | some opt =>
          rw [hf] at h; dsimp only at h
          cases hkb : (opt.kind == .bool) with
          | true =>
            rw [hkb] at h
            rcases ih _ h with ⟨hk, hm, hsh, hhas⟩ | ⟨hk, hm, hsv, hevs, hhas⟩ | herr
            · refine Or.inl ⟨hk, hm, hsh, ?_⟩
              unfold Model.hasShortPrefixBeforeCharBool
              by_cases hch : c = 'h'
              · simp [hch]
              · simp [beq_false_of_ne hch, hf, hkb, hhas]
            · refine Or.inr (Or.inl ⟨hk, hm, hsv, hevs, ?_⟩)
              unfold Model.hasShortPrefixBeforeCharBool
              by_cases hcV : c = 'V'
              · simp [hcV]
              · simp [beq_false_of_ne hcV, hf, hkb, hhas]
            · exact Or.inr (Or.inr herr)
          | false =>
            rw [hkb] at h
            cases hne : (!rest.isEmpty) with
            | false => rw [hne] at h; cases h
            | true =>
              rw [hne] at h; dsimp only [Bind.bind, Except.bind] at h
              rw [parseOptValueWithFast_eq] at h
              cases hp : Model.parseOptValueWith opt.kind (String.ofList rest) validators with
              | ok _ => rw [hp] at h; cases h
              | error e0 =>
                rw [hp] at h; dsimp only at h; injection h with he; subst he
                obtain ⟨hm, hk⟩ := parseOptValueWith_err_props hp
                exact Or.inr (Or.inr ⟨hm, hk ▸ otherErrKind_invalidValue⟩)

private theorem parseShortBundle_ok_decomp (visibleOpts : List OptSpec)
    (shortHelp shortVersion : Bool) (rootName : String) (subPath : List String)
    (effVer : Option String) (curSpec : CommandSpec) (validators : CustomValidators)
    (cliOpts : List (String × List OptValue)) (cs : List Char)
    {nextCli : List (String × List OptValue)} {nextPend : Option OptSpec}
    (h : Internal.parseShortBundle visibleOpts shortHelp shortVersion rootName subPath
      effVer curSpec validators cliOpts cs = .ok (nextCli, nextPend)) :
    (nextPend = none ∧ ∃ onames : List String, Model.validShortBoolPrefixBool visibleOpts cs onames = true) ∨
    (nextPend = none ∧
      ∃ (pcs : List Char) (pnames : List String) (oc : Char) (rv : List Char) (o : OptSpec) (val : OptValue),
        cs = pcs ++ (oc :: rv) ∧ (!rv.isEmpty) = true ∧
        Model.validShortBoolPrefixBool visibleOpts pcs pnames = true ∧
        visibleOpts.find? (fun x => x.short == some oc) = some o ∧
        (o.kind != .bool) = true ∧
        Model.parseOptValueWith o.kind (String.ofList rv) validators = .ok val) ∨
    (∃ (pcs : List Char) (pnames : List String) (oc : Char) (o : OptSpec),
      nextPend = some o ∧ cs = pcs ++ [oc] ∧
      Model.validShortBoolPrefixBool visibleOpts pcs pnames = true ∧
      visibleOpts.find? (fun x => x.short == some oc) = some o ∧
      (o.kind != .bool) = true) := by
  induction cs generalizing cliOpts with
  | nil =>
    unfold Internal.parseShortBundle at h
    injection h with hp; rcases Prod.mk.inj hp with ⟨_, hpn⟩
    exact Or.inl ⟨hpn.symm, [], rfl⟩
  | cons c rest ih =>
    unfold Internal.parseShortBundle at h
    cases hh : (c == 'h' && shortHelp) with
    | true => rw [hh] at h; cases h
    | false =>
      rw [hh] at h
      cases hv : (c == 'V' && shortVersion && effVer.isSome) with
      | true => rw [hv] at h; cases effVer <;> cases h
      | false =>
        rw [hv] at h
        cases hf : visibleOpts.find? (fun o => o.short == some c) with
        | none => rw [hf] at h; cases h
        | some opt =>
          rw [hf] at h; dsimp only at h
          cases hkb : (opt.kind == .bool) with
          | true =>
            rw [hkb] at h
            rcases ih _ h with ⟨hpn, onames, hv_sub⟩ |
              ⟨hpn, pcs, pnames, oc, rv, o, val, hcs_eq, hrv_ne, hv_sub, hfo, hnk, hpv⟩ |
              ⟨pcs, pnames, oc, o, hpn, hcs_eq, hv_sub, hfo, hnk⟩
            · refine Or.inl ⟨hpn, opt.name :: onames, ?_⟩
              unfold Model.validShortBoolPrefixBool
              simp [hf, hkb, hv_sub]
            · refine Or.inr (Or.inl ⟨hpn, c :: pcs, opt.name :: pnames, oc, rv, o, val,
                by rw [hcs_eq]; rfl, hrv_ne, ?_, hfo, hnk, hpv⟩)
              unfold Model.validShortBoolPrefixBool
              simp [hf, hkb, hv_sub]
            · refine Or.inr (Or.inr ⟨c :: pcs, opt.name :: pnames, oc, o, hpn,
                by rw [hcs_eq]; rfl, ?_, hfo, hnk⟩)
              unfold Model.validShortBoolPrefixBool
              simp [hf, hkb, hv_sub]
          | false =>
            rw [hkb] at h
            have hnk : (opt.kind != .bool) = true := by simp [bne, hkb]
            cases hne : (!rest.isEmpty) with
            | true =>
              rw [hne] at h; dsimp only [Bind.bind, Except.bind] at h
              rw [parseOptValueWithFast_eq] at h
              cases hp : Model.parseOptValueWith opt.kind (String.ofList rest) validators with
              | error _ => rw [hp] at h; cases h
              | ok val =>
                rw [hp] at h; dsimp only at h
                injection h with hp2; rcases Prod.mk.inj hp2 with ⟨_, hpn⟩
                exact Or.inr (Or.inl ⟨hpn.symm, [], [], c, rest, opt, val,
                  rfl, hne, rfl, hf, hnk, hp⟩)
            | false =>
              rw [hne] at h
              have hrest_nil : rest = [] := by
                cases rest with | nil => rfl | cons _ _ => cases hne
              subst hrest_nil
              injection h with hp2; rcases Prod.mk.inj hp2 with ⟨_, hpn⟩
              exact Or.inr (Or.inr ⟨[], [], c, opt, hpn.symm, rfl, rfl, hf, hnk⟩)

private theorem runOpenCliPhrases_snoc {validators : CustomValidators}
    {g0 : List OptSpec} {v0 : Option String} {s0 : CommandSpec} {sp0 : Bool}
    {pre : List Model.CliPhrase}
    {g1 : List OptSpec} {v1 : Option String} {s1 : CommandSpec} {sp1 : Bool}
    {p : Model.CliPhrase}
    {g2 : List OptSpec} {v2 : Option String} {s2 : CommandSpec} {sp2 : Bool}
    (hpre : Model.runOpenCliPhrases validators g0 v0 s0 sp0 pre = some (g1, v1, s1, sp1))
    (hp : Model.validSinglePhraseStep validators g1 v1 s1 sp1 p = some (g2, v2, s2, sp2, false)) :
    Model.runOpenCliPhrases validators g0 v0 s0 sp0 (pre ++ [p]) = some (g2, v2, s2, sp2) := by
  induction pre generalizing g0 v0 s0 sp0 with
  | nil =>
    unfold Model.runOpenCliPhrases at hpre ⊢
    simp only [Option.some.injEq, Prod.mk.injEq] at hpre
    rcases hpre with ⟨rfl, rfl, rfl, rfl⟩
    simp [hp, Model.runOpenCliPhrases]
  | cons hd tl ih =>
    simp only [List.cons_append, Model.runOpenCliPhrases] at hpre ⊢
    cases hst : Model.validSinglePhraseStep validators g0 v0 s0 sp0 hd with
    | none => rw [hst] at hpre; cases hpre
    | some tup =>
      rcases tup with ⟨ng, nv, ns, nsp, me⟩
      rw [hst] at hpre; dsimp only at hpre
      cases me with
      | true => cases hpre
      | false =>
        dsimp only [Bool.false_eq_true, ↓reduceIte] at hpre ⊢
        exact ih hpre

private def ParseTokensClassified (spec : CommandSpec) (validators : CustomValidators)
    (st : Internal.ParseState) (prePhrases : List Model.CliPhrase) (remTokens : List String) : Prop :=
  (∃ postPhrases : List Model.CliPhrase,
    (postPhrases.map Model.CliPhrase.tokens).flatten = remTokens ∧
    Model.checkCliPhrases validators st.inheritedGlobals st.effectiveVersion
      st.curSpec (!st.rawPositionals.isEmpty) postPhrases = true) ∨
  (∃ e : CmdLineError,
    Internal.parseTokens spec.name validators st remTokens = .error e ∧
    ((e.kind = .helpRequested ∧ (!e.message.isEmpty) = true ∧
        Model.ExistsHelpInvocation spec validators ((prePhrases.map Model.CliPhrase.tokens).flatten ++ remTokens)) ∨
     (e.kind = .versionRequested ∧ (!e.message.isEmpty) = true ∧
        Model.ExistsVersionInvocation spec validators ((prePhrases.map Model.CliPhrase.tokens).flatten ++ remTokens)) ∨
     ((!e.message.isEmpty) = true ∧ OtherErrKind e.kind)))

private theorem complete_via_open_phrase {spec : CommandSpec} {validators : CustomValidators}
    {st : Internal.ParseState} {prePhrases : List Model.CliPhrase}
    {p : Model.CliPhrase} {rest' remTokens : List String}
    {nextG : List OptSpec} {nextVer : Option String} {nextSpec : CommandSpec} {nextSeenPos : Bool}
    (hinv : ParseStateInv spec st) (hp_none : st.pendingOpt = none) (had_false : st.afterDashDash = false)
    (hopen : Model.runOpenCliPhrases validators [] spec.version spec false prePhrases =
      some (st.inheritedGlobals, st.effectiveVersion, st.curSpec, !st.rawPositionals.isEmpty))
    (hrem : remTokens = p.tokens ++ rest')
    (hstep_p : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
      st.curSpec (!st.rawPositionals.isEmpty) p = some (nextG, nextVer, nextSpec, nextSeenPos, false))
    (hrec : ∀ (st1 : Internal.ParseState),
      ParseStateInv spec st1 → st1.pendingOpt = none → st1.afterDashDash = false →
      Model.runOpenCliPhrases validators [] spec.version spec false (prePhrases ++ [p]) =
        some (st1.inheritedGlobals, st1.effectiveVersion, st1.curSpec, !st1.rawPositionals.isEmpty) →
      ParseTokensClassified spec validators st1 (prePhrases ++ [p]) rest') :
    ParseTokensClassified spec validators st prePhrases remTokens := by
  obtain ⟨st1, hloop1, hspec1, hg1, hver1, _, hp1, had1, _, hseen1, _⟩ :=
    singlePhrase_sound hinv hp_none had_false hstep_p
  have hinv1 := parseTokensLoop_sound spec st hinv p.tokens hloop1
  have hopen1 : Model.runOpenCliPhrases validators [] spec.version spec false (prePhrases ++ [p]) =
      some (st1.inheritedGlobals, st1.effectiveVersion, st1.curSpec, !st1.rawPositionals.isEmpty) := by
    rw [hg1, hver1, hspec1, hseen1]
    exact runOpenCliPhrases_snoc hopen hstep_p
  have hpt_eq : Internal.parseTokens spec.name validators st remTokens =
      Internal.parseTokens spec.name validators st1 rest' := by
    subst hrem
    unfold Internal.parseTokens
    rw [parseTokensLoop_append spec.name validators p.tokens rest' st st1 hloop1]
  have hflat_eq : ((prePhrases ++ [p]).map Model.CliPhrase.tokens).flatten ++ rest' =
      (prePhrases.map Model.CliPhrase.tokens).flatten ++ remTokens := by
    subst hrem
    simp [List.map_append, List.flatten_append, List.append_assoc]
  rcases hrec st1 hinv1 hp1 had1 hopen1 with ⟨post, hpost_tok, hpost_chk⟩ | ⟨e, herr, hcls⟩
  · refine Or.inl ⟨p :: post, ?_, ?_⟩
    · simp only [List.map_cons, List.flatten_cons, hpost_tok]
      exact hrem.symm
    · unfold Model.checkCliPhrases
      rw [hstep_p]; dsimp only [Bool.false_eq_true, ↓reduceIte]
      rw [← hg1, ← hver1, ← hspec1, ← hseen1]
      exact hpost_chk
  · refine Or.inr ⟨e, by rw [hpt_eq]; exact herr, ?_⟩
    rw [hflat_eq] at hcls
    exact hcls

private theorem parseTokens_err_of_step_err {rootName : String} {validators : CustomValidators}
    {st : Internal.ParseState} {tok : String} {rest : List String} {e : CmdLineError}
    (h : Internal.stepToken rootName validators st tok = .error e) :
    Internal.parseTokens rootName validators st (tok :: rest) = .error e := by
  unfold Internal.parseTokens Internal.parseTokensLoop
  simp [h, Bind.bind, Except.bind]

private theorem lookupLongOpt_decomp {opts : List OptSpec} (hnd : (Model.collectVisibleLongs opts).Nodup)
    {namePart : String} {opt : OptSpec} {isNeg : Bool}
    (h : Internal.lookupLongOpt opts namePart = some (opt, isNeg)) :
    (isNeg = false ∧ opts.find? (fun o => o.long == some namePart) = some opt) ∨
    (isNeg = true ∧ ∃ base : String, namePart = "no-" ++ base ∧
      opts.find? (fun o => o.long == some base) = some opt ∧
      (opt.kind == .bool) = true ∧ (!opt.repeatable) = true) := by
  unfold Internal.lookupLongOpt at h
  cases hf : opts.find? (fun o => o.long == some namePart) with
  | some o =>
    rw [hf] at h; injection h with hp
    rcases Prod.mk.inj hp with ⟨ho_eq, hneg_eq⟩
    subst ho_eq hneg_eq
    exact Or.inl ⟨rfl, rfl⟩
  | none =>
    rw [hf] at h; dsimp only at h; rw [internal_startsWithNoDash_eq] at h
    cases hsnd : Model.startsWithNoDash namePart with
    | false => rw [hsnd] at h; cases h
    | true =>
      rw [hsnd] at h; simp only [↓reduceIte] at h
      let base := String.ofList (namePart.toList.drop 3)
      have hnp_eq : namePart = "no-" ++ base := by
        unfold Model.startsWithNoDash at hsnd
        have htake : namePart.toList.take 3 = ['n', 'o', '-'] := beq_iff_eq.mp hsnd
        have hcat := List.take_append_drop 3 namePart.toList
        rw [htake] at hcat
        apply String.ext_iff.mpr
        rw [← hcat, String.toList_append, show "no-".toList = ['n', 'o', '-'] from rfl]
        dsimp only [base]
        rw [String.toList_ofList]
      cases hf2 : opts.find? (fun o => o.kind == .bool && !o.repeatable && o.long == some base) with
      | none => rw [hf2] at h; cases h
      | some o =>
        rw [hf2] at h; injection h with hp
        rcases Prod.mk.inj hp with ⟨ho_eq, hneg_eq⟩
        subst ho_eq hneg_eq
        have hmem := List.mem_of_find?_eq_some hf2
        have hpred := List.find?_some (p := fun (x : OptSpec) => x.kind == .bool && !x.repeatable && x.long == some base) hf2
        simp only [Bool.and_eq_true] at hpred
        have hl : o.long = some base := beq_iff_eq.mp hpred.2
        have hlp := lookupLongOpt_pos opts hnd hmem hl
        have hf_base : opts.find? (fun x => x.long == some base) = some o := by
          unfold Internal.lookupLongOpt at hlp
          cases hfb : opts.find? (fun x => x.long == some base) with
          | some x =>
            rw [hfb] at hlp; injection hlp with hxp
            exact congrArg some (Prod.mk.inj hxp).1
          | none =>
            rw [hfb] at hlp; dsimp only at hlp
            split at hlp
            · cases h2 : opts.find? (fun x => x.kind == .bool && !x.repeatable && x.long == some (String.ofList (base.toList.drop 3))) <;>
                rw [h2] at hlp <;> cases hlp
            · cases hlp
        exact Or.inr ⟨rfl, base, hnp_eq, hf_base, hpred.1.1, hpred.1.2⟩

private theorem stepToken_long_eq {rootName : String} {validators : CustomValidators}
    {st : Internal.ParseState} {tok : String} {rest2 : List Char}
    {namePart : String} {eqVal? : Option String}
    (hp_none : st.pendingOpt = none) (had_false : st.afterDashDash = false)
    (hdd : (tok == "--") = false) (hh : (tok == "--help") = false)
    (hv : (tok == "--version" && st.effectiveVersion.isSome) = false)
    (htl : tok.toList = '-' :: '-' :: rest2) :
    Internal.splitFirstEq (String.ofList rest2) = (namePart, eqVal?) →
    Internal.stepToken rootName validators st tok =
      (let visibleOpts := st.inheritedGlobals ++ st.curSpec.options
       if namePart.isEmpty then
         .error { kind := .unknownOption, message := s!"unknown option '{tok}'", target := some tok }
       else if namePart == "help" || (namePart == "version" && st.effectiveVersion.isSome) then
         .error { kind := .invalidValue, message := s!"option '--{namePart}' does not take a value", target := some namePart }
       else
         match Internal.lookupLongOpt visibleOpts namePart with
         | none =>
           let hint := match Internal.bestSuggestion namePart (Internal.longCandidates visibleOpts st.effectiveVersion) with
             | some cand => s!"; did you mean '--{cand}'?"
             | none => ""
           .error { kind := .unknownOption, message := s!"unknown option '--{namePart}'{hint}", target := some namePart }
         | some (opt, isNegated) =>
           if isNegated then
             match eqVal? with
             | some _ => .error { kind := .invalidValue, message := s!"option '--{namePart}' does not take a value", target := some opt.name }
             | none => .ok { st with cliOpts := Internal.recordCliOpt st.cliOpts opt.name (.bool false) }
           else if opt.kind == .bool then
             match eqVal? with
             | none => .ok { st with cliOpts := Internal.recordCliOpt st.cliOpts opt.name (.bool true) }
             | some rawVal =>
               match Model.parseOptValue .bool rawVal with
               | .error e => .error { e with target := some opt.name }
               | .ok (.bool b) =>
                 if opt.repeatable && !b then
                   .error { kind := .invalidValue, message := s!"repeatable flag '--{namePart}' cannot be set to false", target := some opt.name }
                 else .ok { st with cliOpts := Internal.recordCliOpt st.cliOpts opt.name (.bool b) }
               | .ok _ => .error { kind := .invalidValue, message := "invalid boolean", target := some opt.name }
           else
             match eqVal? with
             | some rawVal =>
               match Internal.parseOptValueWithFast opt.kind rawVal validators with
               | .error e => .error { e with target := some opt.name }
               | .ok v => .ok { st with cliOpts := Internal.recordCliOpt st.cliOpts opt.name v }
             | none => .ok { st with pendingOpt := some opt }) := by
  intro hsf
  unfold Internal.stepToken
  simp only [hp_none, had_false, hdd, hh, hv, Bool.false_eq_true, ↓reduceIte]
  rw [htl]
  split
  · rename_i lr heq
    have hlr := (List.cons.inj (List.cons.inj heq).2).2
    subst hlr
    rw [hsf]
    dsimp only [Bind.bind, Except.bind]
    by_cases h1 : namePart.isEmpty = true
    · simp [h1]
    · by_cases h2 : (namePart == "help" || (namePart == "version" && st.effectiveVersion.isSome)) = true
      · simp [h1, h2]
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
        cases Internal.lookupLongOpt (st.inheritedGlobals ++ st.curSpec.options) namePart with
        | none => rfl
        | some p =>
          rcases p with ⟨opt, isNegated⟩
          cases isNegated with
          | true => rfl
          | false =>
            by_cases hk : (opt.kind == .bool) = true
            · simp only [hk, ↓reduceIte]
              cases eqVal? with
              | none => rfl
              | some rawVal => dsimp only; rw [Shared.parseOptValueFast_eq]; rfl
            · simp only [hk, Bool.false_eq_true, ↓reduceIte]
              cases eqVal? with
              | none => rfl
              | some rawVal =>
                cases Internal.parseOptValueWithFast opt.kind rawVal validators <;> rfl
  · rename_i _ _ hne_d heq
    have hc := (List.cons.inj (List.cons.inj heq).2).1
    exact absurd hc.symm hne_d
  · rename_i _ h1 _; exact absurd rfl (h1 rest2)

private theorem parseTokens_complete_or_err_aux {spec : CommandSpec} {validators : CustomValidators} :
    ∀ (n : Nat) (remTokens : List String) (st : Internal.ParseState) (prePhrases : List Model.CliPhrase),
      remTokens.length ≤ n →
      ParseStateInv spec st →
      st.pendingOpt = none →
      st.afterDashDash = false →
      Model.runOpenCliPhrases validators [] spec.version spec false prePhrases =
        some (st.inheritedGlobals, st.effectiveVersion, st.curSpec, !st.rawPositionals.isEmpty) →
      ParseTokensClassified spec validators st prePhrases remTokens := by
  intro n
  induction n with
  | zero =>
    intro remTokens st _ hlen _ _ _ _
    have hnil : remTokens = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst hnil
    exact Or.inl ⟨[], rfl, rfl⟩
  | succ m ih =>
    intro remTokens st prePhrases hlen hinv hp_none had_false hopen
    cases remTokens with
    | nil => exact Or.inl ⟨[], rfl, rfl⟩
    | cons tok rest =>
      have hrest_le : rest.length ≤ m := Nat.le_of_succ_le_succ hlen
      rcases hinv with ⟨⟨vp, hnode, heff⟩, hpath, hcli, hpend⟩
      have hinv_full : ParseStateInv spec st := ⟨⟨vp, hnode, heff⟩, hpath, hcli, hpend⟩
      have hprops := nodeInv_props hnode
      cases hdd : (tok == "--") with
      | true =>
        have htok_eq : tok = "--" := beq_iff_eq.mp hdd
        subst htok_eq
        refine Or.inl ⟨[Model.CliPhrase.dashDashTail rest], ?_, ?_⟩
        · simp [Model.CliPhrase.tokens]
        · simp [Model.checkCliPhrases, Model.validSinglePhraseStep]
      | false =>
        cases hh : (tok == "--help") with
        | true =>
          have htok_eq : tok = "--help" := beq_iff_eq.mp hh
          subst htok_eq
          have hst_err : Internal.stepToken spec.name validators st "--help" =
              .error { kind := .helpRequested,
                       message := Internal.renderHelpNode (spec.name :: st.subPath)
                         (st.inheritedGlobals ++ st.curSpec.options) st.effectiveVersion st.curSpec } := by
            unfold Internal.stepToken
            simp [hp_none, had_false, hdd]
          refine Or.inr ⟨_, parseTokens_err_of_step_err hst_err, Or.inl ⟨rfl,
            renderHelpNode_nonEmpty_shared (spec.name :: st.subPath)
              (st.inheritedGlobals ++ st.curSpec.options) st.effectiveVersion st.curSpec,
            ⟨prePhrases, "--help", rest, st.inheritedGlobals, st.effectiveVersion, st.curSpec,
              !st.rawPositionals.isEmpty, hopen, rfl, by simp [Model.isHelpTriggerTokenBool]⟩⟩⟩
        | false =>
          cases hv : (tok == "--version" && st.effectiveVersion.isSome) with
          | true =>
            rw [Bool.and_eq_true] at hv
            have htok_eq : tok = "--version" := beq_iff_eq.mp hv.1
            subst htok_eq
            cases hev : st.effectiveVersion with
            | none => simp [hev] at hv
            | some verStr =>
              have hst_err : Internal.stepToken spec.name validators st "--version" =
                  .error { kind := .versionRequested, message := Internal.renderVersion spec.name verStr } := by
                unfold Internal.stepToken
                simp [hp_none, had_false, hev]
              refine Or.inr ⟨_, parseTokens_err_of_step_err hst_err, Or.inr (Or.inl ⟨rfl,
                renderVersion_nonEmpty spec.name verStr,
                ⟨prePhrases, "--version", rest, st.inheritedGlobals, some verStr, st.curSpec,
                  !st.rawPositionals.isEmpty, by rw [← hev]; exact hopen, rfl,
                  by simp [Model.isVersionTriggerTokenBool]⟩⟩)⟩
          | false =>
            have hPlainBranch : Model.isPlainCliTokenBool tok = true →
                (∀ c sr, tok.toList ≠ '-' :: c :: sr) →
                ParseTokensClassified spec validators st prePhrases (tok :: rest) := by
              intro hplain hno_dash2
              cases hsc : (!st.curSpec.subcommands.isEmpty && st.rawPositionals.isEmpty) with
              | true =>
                cases hfs : st.curSpec.subcommands.find? (fun s => s.name == tok) with
                | none =>
                  have hst_err : ∃ e, Internal.stepToken spec.name validators st tok = .error e ∧
                      (!e.message.isEmpty) = true ∧ OtherErrKind e.kind := by
                    unfold Internal.stepToken
                    simp only [hp_none, had_false, hdd, hh, hv, Bool.false_eq_true, ↓reduceIte]
                    split
                    · rename_i lr heqm; exact absurd heqm (hno_dash2 '-' lr)
                    · rename_i c sr _ heqm; exact absurd heqm (hno_dash2 c sr)
                    · simp only [hsc, ↓reduceIte, hfs]
                      exact ⟨_, rfl, nonEmpty_str_append_left (nonEmpty_str_append_left (nonEmpty_str_append_left rfl)),
                        otherErrKind_unknownSubcommand⟩
                  obtain ⟨e, hse, hm, hk⟩ := hst_err
                  exact Or.inr ⟨e, parseTokens_err_of_step_err hse, Or.inr (Or.inr ⟨hm, hk⟩)⟩
                | some sub =>
                  have hstep_p : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
                      st.curSpec (!st.rawPositionals.isEmpty) (.subcommand tok) =
                      some (st.inheritedGlobals ++ st.curSpec.options, sub.version <|> st.effectiveVersion, sub, false, false) := by
                    unfold Model.validSinglePhraseStep
                    dsimp only
                    have hcond : (!st.curSpec.subcommands.isEmpty && !!st.rawPositionals.isEmpty) = true := by
                      simpa using hsc
                    rw [hcond, hfs]; rfl
                  exact complete_via_open_phrase hinv_full hp_none had_false hopen rfl hstep_p
                    (fun st1 hi1 hp1 ha1 ho1 => ih rest st1 _ hrest_le hi1 hp1 ha1 ho1)
              | false =>
                have hleaf_or_seen : (st.curSpec.subcommands.isEmpty || !st.rawPositionals.isEmpty) = true := by
                  cases h1 : st.curSpec.subcommands.isEmpty <;> cases h2 : st.rawPositionals.isEmpty <;> simp_all
                have hstep_p : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
                    st.curSpec (!st.rawPositionals.isEmpty) (.positional tok) =
                    some (st.inheritedGlobals, st.effectiveVersion, st.curSpec, true, false) := by
                  unfold Model.validSinglePhraseStep
                  simp [hplain, hleaf_or_seen]
                exact complete_via_open_phrase hinv_full hp_none had_false hopen rfl hstep_p
                  (fun st1 hi1 hp1 ha1 ho1 => ih rest st1 _ hrest_le hi1 hp1 ha1 ho1)
            cases htl : tok.toList with
            | nil =>
              exact hPlainBranch (by unfold Model.isPlainCliTokenBool; rw [htl])
                (fun _ _ heq => by rw [htl] at heq; cases heq)
            | cons c1 rest1 =>
              by_cases hc1 : c1 = '-'
              · subst hc1
                cases rest1 with
                | nil =>
                  exact hPlainBranch (by unfold Model.isPlainCliTokenBool; rw [htl]; rfl)
                    (fun _ _ heq => by rw [htl] at heq; cases heq)
                | cons c2 rest2 =>
                  by_cases hc2 : c2 = '-'
                  · subst hc2
                    have hsfd := splitFirstEq_decomp (String.ofList rest2)
                    cases hsf : Internal.splitFirstEq (String.ofList rest2) with
                    | mk namePart eqVal? =>
                      rw [hsf] at hsfd
                      have hstep_long := stepToken_long_eq (rootName := spec.name) (validators := validators)
                        hp_none had_false hdd hh hv htl hsf
                      cases hnp_emp : namePart.isEmpty with
                      | true =>
                        have hse : Internal.stepToken spec.name validators st tok =
                            .error { kind := .unknownOption, message := s!"unknown option '{tok}'", target := some tok } := by
                          rw [hstep_long]; simp [hnp_emp]
                        exact Or.inr ⟨_, parseTokens_err_of_step_err hse, Or.inr (Or.inr
                          ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), otherErrKind_unknownOption⟩)⟩
                      | false =>
                        cases hnhv : (namePart == "help" || (namePart == "version" && st.effectiveVersion.isSome)) with
                        | true =>
                          have hse : Internal.stepToken spec.name validators st tok =
                              .error { kind := .invalidValue, message := s!"option '--{namePart}' does not take a value", target := some namePart } := by
                            rw [hstep_long]; simp [hnp_emp, hnhv]
                          exact Or.inr ⟨_, parseTokens_err_of_step_err hse, Or.inr (Or.inr
                            ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), otherErrKind_invalidValue⟩)⟩
                        | false =>
                          cases hlkp : Internal.lookupLongOpt (st.inheritedGlobals ++ st.curSpec.options) namePart with
                          | none =>
                            have hse : ∃ e, Internal.stepToken spec.name validators st tok = .error e ∧
                                (!e.message.isEmpty) = true ∧ OtherErrKind e.kind := by
                              rw [hstep_long]; dsimp only
                              rw [hnp_emp, hnhv, hlkp]
                              exact ⟨_, rfl, nonEmpty_str_append_left (nonEmpty_str_append_left (nonEmpty_str_append_left rfl)),
                                otherErrKind_unknownOption⟩
                            obtain ⟨e, hse_eq, hm, hk⟩ := hse
                            exact Or.inr ⟨e, parseTokens_err_of_step_err hse_eq, Or.inr (Or.inr ⟨hm, hk⟩)⟩
                          | some pair =>
                            rcases pair with ⟨opt, isNeg⟩
                            rcases lookupLongOpt_decomp hprops.nodupLongs hlkp with
                              ⟨hisNeg, hf_pos⟩ | ⟨hisNeg, base, hnp_base, hf_base, hkb, hnr⟩
                            · subst hisNeg
                              cases hkb_pos : (opt.kind == .bool) with
                              | true =>
                                cases eqVal? with
                                | none =>
                                  have htok_eq : tok = "--" ++ namePart := by
                                    have hsr := congrArg String.toList hsfd.2
                                    rw [String.toList_ofList] at hsr
                                    apply String.ext_iff.mpr
                                    rw [htl, ← hsr, String.toList_append]; rfl
                                  have hstep_p : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
                                      st.curSpec (!st.rawPositionals.isEmpty) (.longBoolTrue namePart opt.name) =
                                      some (st.inheritedGlobals, st.effectiveVersion, st.curSpec, !st.rawPositionals.isEmpty, false) := by
                                    unfold Model.validSinglePhraseStep; dsimp only
                                    rw [hf_pos]; simp [hkb_pos]
                                  exact complete_via_open_phrase hinv_full hp_none had_false hopen
                                    (by simp [Model.CliPhrase.tokens, htok_eq]) hstep_p
                                    (fun st1 hi1 hp1 ha1 ho1 => ih rest st1 _ hrest_le hi1 hp1 ha1 ho1)
                                | some rv =>
                                  have htok_eq : tok = "--" ++ namePart ++ "=" ++ rv := by
                                    have hsr := congrArg String.toList hsfd.2
                                    rw [String.toList_ofList] at hsr
                                    apply String.ext_iff.mpr
                                    rw [htl, hsr]; simp [String.toList_append, List.append_assoc]
                                  cases hpv : Model.parseOptValue .bool rv with
                                  | error e0 =>
                                    have hse : Internal.stepToken spec.name validators st tok =
                                        .error { e0 with target := some opt.name } := by
                                      rw [hstep_long]; dsimp only
                                      rw [hnp_emp, hnhv, hlkp]; simp [hkb_pos, hpv]
                                    obtain ⟨hm, hk⟩ := parseOptValue_err_props hpv
                                    exact Or.inr ⟨_, parseTokens_err_of_step_err hse, Or.inr (Or.inr
                                      ⟨hm, hk ▸ otherErrKind_invalidValue⟩)⟩
                                  | ok ov =>
                                    have hmKind := parseOptValue_ok_matchesKind hpv
                                    cases ov with
                                    | string _ | nat _ | int _ | choice _ | custom _ => cases hmKind
                                    | bool b =>
                                      cases hrb : (opt.repeatable && !b) with
                                      | true =>
                                        have hse : Internal.stepToken spec.name validators st tok =
                                            .error { kind := .invalidValue,
                                                     message := s!"repeatable flag '--{namePart}' cannot be set to false",
                                                     target := some opt.name } := by
                                          rw [hstep_long]; dsimp only
                                          rw [hnp_emp, hnhv, hlkp]; simp [hkb_pos, hpv, hrb]
                                        exact Or.inr ⟨_, parseTokens_err_of_step_err hse, Or.inr (Or.inr
                                          ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), otherErrKind_invalidValue⟩)⟩
                                      | false =>
                                        have hpbs : (Model.parseBoolString rv == some b) = true := by
                                          unfold Model.parseOptValue at hpv
                                          cases hb : Model.parseBoolString rv with
                                          | none => rw [hb] at hpv; cases hpv
                                          | some b0 => rw [hb] at hpv; injection hpv with h1; injection h1 with h2; subst h2; simp
                                        have hstep_p : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
                                            st.curSpec (!st.rawPositionals.isEmpty) (.longBoolEq namePart rv opt.name b) =
                                            some (st.inheritedGlobals, st.effectiveVersion, st.curSpec, !st.rawPositionals.isEmpty, false) := by
                                          unfold Model.validSinglePhraseStep; dsimp only
                                          rw [hf_pos]; simp [hkb_pos, hrb, hpbs]
                                        exact complete_via_open_phrase hinv_full hp_none had_false hopen
                                          (by simp [Model.CliPhrase.tokens, htok_eq]) hstep_p
                                          (fun st1 hi1 hp1 ha1 ho1 => ih rest st1 _ hrest_le hi1 hp1 ha1 ho1)
                              | false =>
                                have hnk_b : (opt.kind != .bool) = true := by simp [bne, hkb_pos]
                                cases eqVal? with
                                | some rv =>
                                  have htok_eq : tok = "--" ++ namePart ++ "=" ++ rv := by
                                    have hsr := congrArg String.toList hsfd.2
                                    rw [String.toList_ofList] at hsr
                                    apply String.ext_iff.mpr
                                    rw [htl, hsr]; simp [String.toList_append, List.append_assoc]
                                  cases hpv : Model.parseOptValueWith opt.kind rv validators with
                                  | error e0 =>
                                    have hse : Internal.stepToken spec.name validators st tok =
                                        .error { e0 with target := some opt.name } := by
                                      rw [hstep_long]; dsimp only
                                      rw [hnp_emp, hnhv, hlkp]; simp [hkb_pos, parseOptValueWithFast_eq, hpv]
                                    obtain ⟨hm, hk⟩ := parseOptValueWith_err_props hpv
                                    exact Or.inr ⟨_, parseTokens_err_of_step_err hse, Or.inr (Or.inr
                                      ⟨hm, hk ▸ otherErrKind_invalidValue⟩)⟩
                                  | ok val =>
                                    have hstep_p : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
                                        st.curSpec (!st.rawPositionals.isEmpty) (.longValEq namePart rv opt.name val) =
                                        some (st.inheritedGlobals, st.effectiveVersion, st.curSpec, !st.rawPositionals.isEmpty, false) := by
                                      unfold Model.validSinglePhraseStep; dsimp only
                                      rw [hf_pos]; simp [hnk_b, hpv]
                                    exact complete_via_open_phrase hinv_full hp_none had_false hopen
                                      (by simp [Model.CliPhrase.tokens, htok_eq]) hstep_p
                                      (fun st1 hi1 hp1 ha1 ho1 => ih rest st1 _ hrest_le hi1 hp1 ha1 ho1)
                                | none =>
                                  have htok_eq : tok = "--" ++ namePart := by
                                    have hsr := congrArg String.toList hsfd.2
                                    rw [String.toList_ofList] at hsr
                                    apply String.ext_iff.mpr
                                    rw [htl, ← hsr, String.toList_append]; rfl
                                  have hse1 : Internal.stepToken spec.name validators st tok =
                                      .ok { st with pendingOpt := some opt } := by
                                    rw [hstep_long]; dsimp only
                                    rw [hnp_emp, hnhv, hlkp]; simp [hkb_pos]
                                  cases rest with
                                  | nil =>
                                    have hpt_err : Internal.parseTokens spec.name validators st [tok] =
                                        .error { kind := .missingArgument,
                                                 message := s!"option '{opt.name}' requires a value",
                                                 target := some opt.name } := by
                                      unfold Internal.parseTokens Internal.parseTokensLoop
                                      rw [hse1]; dsimp only [Bind.bind, Except.bind]
                                      rfl
                                    exact Or.inr ⟨_, hpt_err, Or.inr (Or.inr
                                      ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), otherErrKind_missingArgument⟩)⟩
                                  | cons rv rest2 =>
                                    have hrest2_le : rest2.length ≤ m := Nat.le_of_lt hrest_le
                                    cases hpv : Model.parseOptValueWith opt.kind rv validators with
                                    | error e0 =>
                                      have hpt_err : Internal.parseTokens spec.name validators st (tok :: rv :: rest2) =
                                          .error { e0 with target := some opt.name } := by
                                        unfold Internal.parseTokens Internal.parseTokensLoop
                                        rw [hse1]; dsimp only [Bind.bind, Except.bind]
                                        unfold Internal.parseTokensLoop Internal.stepToken
                                        simp [parseOptValueWithFast_eq, hpv, Bind.bind, Except.bind]
                                      obtain ⟨hm, hk⟩ := parseOptValueWith_err_props hpv
                                      exact Or.inr ⟨_, hpt_err, Or.inr (Or.inr ⟨hm, hk ▸ otherErrKind_invalidValue⟩)⟩
                                    | ok val =>
                                      have hstep_p : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
                                          st.curSpec (!st.rawPositionals.isEmpty) (.longValSep namePart rv opt.name val) =
                                          some (st.inheritedGlobals, st.effectiveVersion, st.curSpec, !st.rawPositionals.isEmpty, false) := by
                                        unfold Model.validSinglePhraseStep; dsimp only
                                        rw [hf_pos]; simp [hnk_b, hpv]
                                      exact complete_via_open_phrase hinv_full hp_none had_false hopen
                                        (by simp [Model.CliPhrase.tokens, htok_eq]) hstep_p
                                        (fun st1 hi1 hp1 ha1 ho1 => ih rest2 st1 _ hrest2_le hi1 hp1 ha1 ho1)
                            · subst hisNeg
                              cases eqVal? with
                              | some _ =>
                                have hse : Internal.stepToken spec.name validators st tok =
                                    .error { kind := .invalidValue,
                                             message := s!"option '--{namePart}' does not take a value",
                                             target := some opt.name } := by
                                  rw [hstep_long]; dsimp only
                                  simp [hnp_emp, hnhv, hlkp]
                                exact Or.inr ⟨_, parseTokens_err_of_step_err hse, Or.inr (Or.inr
                                  ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), otherErrKind_invalidValue⟩)⟩
                              | none =>
                                have htok_eq : tok = "--no-" ++ base := by
                                  apply String.ext_iff.mpr
                                  rw [htl, String.toList_append, show "--no-".toList = ['-', '-', 'n', 'o', '-'] from rfl]
                                  have hsr := congrArg String.toList (hsfd.2.symm.trans hnp_base)
                                  rw [String.toList_ofList, String.toList_append,
                                    show "no-".toList = ['n', 'o', '-'] from rfl] at hsr
                                  rw [hsr]; rfl
                                have hstep_p : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
                                    st.curSpec (!st.rawPositionals.isEmpty) (.longBoolNeg base opt.name) =
                                    some (st.inheritedGlobals, st.effectiveVersion, st.curSpec, !st.rawPositionals.isEmpty, false) := by
                                  unfold Model.validSinglePhraseStep; dsimp only
                                  rw [hf_base]; simp [hkb, hnr]
                                exact complete_via_open_phrase hinv_full hp_none had_false hopen
                                  (by simp [Model.CliPhrase.tokens, htok_eq]) hstep_p
                                  (fun st1 hi1 hp1 ha1 ho1 => ih rest st1 _ hrest_le hi1 hp1 ha1 ho1)
                  · have hstep_short : Internal.stepToken spec.name validators st tok =
                        (do
                          let (nextCli, nextPend) ←
                            Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp st.curSpec.shortVersion
                              spec.name st.subPath st.effectiveVersion st.curSpec validators st.cliOpts (c2 :: rest2)
                          .ok { st with cliOpts := nextCli, pendingOpt := nextPend }) := by
                      unfold Internal.stepToken
                      simp only [hp_none, had_false, hdd, hh, hv, Bool.false_eq_true, ↓reduceIte]
                      rw [htl]
                      split
                      · rename_i _ heq; exact absurd (List.cons.inj (List.cons.inj heq).2).1 hc2
                      · rename_i _ c' sr' _ heq
                        have hc' := (List.cons.inj (List.cons.inj heq).2).1
                        have hsr' := (List.cons.inj (List.cons.inj heq).2).2
                        subst hc' hsr'; rfl
                      · rename_i _ _ h2; exact absurd rfl (h2 c2 rest2)
                    have htok_ofList : String.ofList ('-' :: c2 :: rest2) = tok := by
                      rw [← htl, String.ofList_toList]
                    cases hsb : Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp st.curSpec.shortVersion
                        spec.name st.subPath st.effectiveVersion st.curSpec validators st.cliOpts (c2 :: rest2) with
                    | error e =>
                      have hse : Internal.stepToken spec.name validators st tok = .error e := by
                        rw [hstep_short, hsb]; rfl
                      have hpt_err := parseTokens_err_of_step_err (rest := rest) hse
                      rcases parseShortBundle_err_classify (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp st.curSpec.shortVersion
                          spec.name st.subPath st.effectiveVersion st.curSpec validators st.cliOpts (c2 :: rest2) hsb with
                        ⟨hk, hm, hsh, hhas⟩ | ⟨hk, hm, hsv, hevs, hhas⟩ | herr
                      · refine Or.inr ⟨e, hpt_err, Or.inl ⟨hk, hm,
                          ⟨prePhrases, tok, rest, st.inheritedGlobals, st.effectiveVersion, st.curSpec,
                            !st.rawPositionals.isEmpty, hopen, rfl, ?_⟩⟩⟩
                        unfold Model.isHelpTriggerTokenBool
                        rw [hh, Bool.false_or, htl]
                        simp [hsh, bne_iff_ne, hc2, hhas]
                      · refine Or.inr ⟨e, hpt_err, Or.inr (Or.inl ⟨hk, hm,
                          ⟨prePhrases, tok, rest, st.inheritedGlobals, st.effectiveVersion, st.curSpec,
                            !st.rawPositionals.isEmpty, hopen, rfl, ?_⟩⟩)⟩
                        unfold Model.isVersionTriggerTokenBool
                        rw [hevs, Bool.true_and]
                        by_cases htv : (tok == "--version") = true
                        · simp [htv]
                        · rw [Bool.eq_false_iff.mpr htv, Bool.false_or, htl]
                          simp [hsv, bne_iff_ne, hc2, hhas]
                      · exact Or.inr ⟨e, hpt_err, Or.inr (Or.inr herr)⟩
                    | ok pair =>
                      rcases pair with ⟨nextCli, nextPend⟩
                      rcases parseShortBundle_ok_decomp (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp st.curSpec.shortVersion
                          spec.name st.subPath st.effectiveVersion st.curSpec validators st.cliOpts (c2 :: rest2) hsb with
                        ⟨_, onames, hv_b⟩ |
                        ⟨_, pcs, pnames, oc, rv, o, val, hcs_eq, hrv_ne, hv_pre, hfo, hnk, hpv⟩ |
                        ⟨pcs, pnames, oc, o, hpn, hcs_eq, hv_pre, hfo, hnk⟩
                      · have hstep_p : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
                            st.curSpec (!st.rawPositionals.isEmpty) (.shortBoolCluster (c2 :: rest2) onames) =
                            some (st.inheritedGlobals, st.effectiveVersion, st.curSpec, !st.rawPositionals.isEmpty, false) := by
                          unfold Model.validSinglePhraseStep; dsimp only
                          simp [hv_b]
                        exact complete_via_open_phrase hinv_full hp_none had_false hopen
                          (by simp [Model.CliPhrase.tokens, htok_ofList]) hstep_p
                          (fun st1 hi1 hp1 ha1 ho1 => ih rest st1 _ hrest_le hi1 hp1 ha1 ho1)
                      · have hstep_p : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
                            st.curSpec (!st.rawPositionals.isEmpty) (.shortAttachedVal pcs pnames oc rv o.name val) =
                            some (st.inheritedGlobals, st.effectiveVersion, st.curSpec, !st.rawPositionals.isEmpty, false) := by
                          unfold Model.validSinglePhraseStep; dsimp only
                          rw [hfo]; simp [hrv_ne, hv_pre, hnk, hpv]
                        exact complete_via_open_phrase hinv_full hp_none had_false hopen
                          (by simp [Model.CliPhrase.tokens, ← hcs_eq, htok_ofList]) hstep_p
                          (fun st1 hi1 hp1 ha1 ho1 => ih rest st1 _ hrest_le hi1 hp1 ha1 ho1)
                      · subst hpn
                        have hse1 : Internal.stepToken spec.name validators st tok =
                            .ok { st with cliOpts := nextCli, pendingOpt := some o } := by
                          rw [hstep_short, hsb]; rfl
                        cases rest with
                        | nil =>
                          have hpt_err : Internal.parseTokens spec.name validators st [tok] =
                              .error { kind := .missingArgument,
                                       message := s!"option '{o.name}' requires a value",
                                       target := some o.name } := by
                            unfold Internal.parseTokens Internal.parseTokensLoop
                            rw [hse1]; dsimp only [Bind.bind, Except.bind]
                            rfl
                          exact Or.inr ⟨_, hpt_err, Or.inr (Or.inr
                            ⟨nonEmpty_str_append_left (nonEmpty_str_append_left rfl), otherErrKind_missingArgument⟩)⟩
                        | cons rv rest2 =>
                          have hrest2_le : rest2.length ≤ m := Nat.le_of_lt hrest_le
                          cases hpv : Model.parseOptValueWith o.kind rv validators with
                          | error e0 =>
                            have hpt_err : Internal.parseTokens spec.name validators st (tok :: rv :: rest2) =
                                .error { e0 with target := some o.name } := by
                              unfold Internal.parseTokens Internal.parseTokensLoop
                              rw [hse1]; dsimp only [Bind.bind, Except.bind]
                              unfold Internal.parseTokensLoop Internal.stepToken
                              simp [parseOptValueWithFast_eq, hpv, Bind.bind, Except.bind]
                            obtain ⟨hm, hk⟩ := parseOptValueWith_err_props hpv
                            exact Or.inr ⟨_, hpt_err, Or.inr (Or.inr ⟨hm, hk ▸ otherErrKind_invalidValue⟩)⟩
                          | ok val =>
                            have hstep_p : Model.validSinglePhraseStep validators st.inheritedGlobals st.effectiveVersion
                                st.curSpec (!st.rawPositionals.isEmpty) (.shortSepVal pcs pnames oc rv o.name val) =
                                some (st.inheritedGlobals, st.effectiveVersion, st.curSpec, !st.rawPositionals.isEmpty, false) := by
                              unfold Model.validSinglePhraseStep; dsimp only
                              rw [hfo]; simp [hv_pre, hnk, hpv]
                            exact complete_via_open_phrase hinv_full hp_none had_false hopen
                              (by simp [Model.CliPhrase.tokens, ← hcs_eq, htok_ofList]) hstep_p
                              (fun st1 hi1 hp1 ha1 ho1 => ih rest2 st1 _ hrest2_le hi1 hp1 ha1 ho1)
              · exact hPlainBranch
                  (by
                    unfold Model.isPlainCliTokenBool
                    rw [htl]
                    split
                    · rename_i _ _ heq; exact absurd (List.cons.inj heq).1 hc1
                    · rfl)
                  (fun _ _ heq => by rw [htl] at heq; exact hc1 (List.cons.inj heq).1)

/-- Full soundness and completeness bridge: `Internal.parseWithEnvSpecM` satisfies `Model.AllowedParseOutcome`. -/
theorem parseWithEnvSpecM_allowedOutcome {W : Type} {ops : CliOpsM (StateM W)}
    {getEnv : String → Except CmdLineError (Option String)} {w : W}
    {spec : CommandSpec} {args : List String} {validators : CustomValidators}
    (hro_eq : ∀ visibleOpts cliOpts,
      (Internal.resolveOptionsTR ops.getEnv visibleOpts cliOpts validators w).1 =
        Model.resolveOptions (m := Id) getEnv visibleOpts cliOpts validators) :
    Model.AllowedParseOutcome getEnv spec args validators
      (Internal.parseWithEnvSpecM ops spec args validators w).1 := by
  unfold Model.AllowedParseOutcome
  cases hv : Model.isValidSpec spec with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    unfold Internal.parseWithEnvSpecM
    rw [isValidSpecTR_eq, hv]
    rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hNoValidOfErr : ∀ {e : CmdLineError},
        (Internal.parseWithEnvSpecM ops spec args validators w).1 = .error e →
        ¬(∃ parsed, Model.ValidParsedCmd getEnv spec args validators parsed) := by
      intro e herr ⟨parsed, hvp⟩
      have hok := validParsedCmd_sound (w := w) hro_eq hvp
      rw [herr] at hok; cases hok
    have hNoHelpOfPtOk : ∀ {st1 : Internal.ParseState},
        Internal.parseTokens spec.name validators { curSpec := spec, effectiveVersion := spec.version } args = .ok st1 →
        ¬Model.ExistsHelpInvocation spec validators args := by
      intro st1 hok hhelp
      obtain ⟨_, herr, _, _⟩ := existsHelpInvocation_sound hv hhelp
      rw [hok] at herr; cases herr
    have hNoVerOfPtOk : ∀ {st1 : Internal.ParseState},
        Internal.parseTokens spec.name validators { curSpec := spec, effectiveVersion := spec.version } args = .ok st1 →
        ¬Model.ExistsVersionInvocation spec validators args := by
      intro st1 hok hver
      obtain ⟨_, herr, _, _⟩ := existsVersionInvocation_sound hv hver
      rw [hok] at herr; cases herr
    have hcls := parseTokens_complete_or_err_aux (validators := validators) args.length args
      { curSpec := spec, effectiveVersion := spec.version } [] (Nat.le_refl _)
      (initParseStateInv hv) rfl rfl rfl
    rcases hcls with ⟨phrases, hargs_eq, hchk_ok⟩ | ⟨e, hpt_err, herr_cls⟩
    · have hinv0 := initParseStateInv hv
      obtain ⟨loopSt, hloop, hp_none, hsub_st, hpos_st, hcli_st⟩ :=
        checkCliPhrases_sound { curSpec := spec, effectiveVersion := spec.version } phrases hinv0 rfl rfl hchk_ok
      simp only [List.nil_append, List.append_nil] at hsub_st hpos_st
      let finalSt : Internal.ParseState :=
        { loopSt with
          cliOpts := loopSt.cliOpts.map (fun p => (p.1, p.2.reverse)),
          rawPositionals := loopSt.rawPositionals.reverse }
      have hpt_ok : Internal.parseTokens spec.name validators
          { curSpec := spec, effectiveVersion := spec.version } args = .ok finalSt := by
        rw [← hargs_eq]
        unfold Internal.parseTokens
        simp [hloop, hp_none, Bind.bind, Except.bind, finalSt]
      have ⟨hinv_final, _⟩ := parseTokens_sound spec { curSpec := spec, effectiveVersion := spec.version } hinv0 args hpt_ok
      rcases hinv_final with ⟨⟨vp_f, hnode_f, _⟩, hpath_f, _, _⟩
      dsimp only [finalSt] at hnode_f hpath_f
      have hprops_f := nodeInv_props hnode_f
      have hlkp_eq : ∀ opt ∈ loopSt.inheritedGlobals ++ loopSt.curSpec.options,
          lookupCli finalSt.cliOpts opt.name =
            lookupCli (Model.cliOptsOfPhrases (loopSt.inheritedGlobals ++ loopSt.curSpec.options) phrases) opt.name := by
        intro opt ho
        dsimp only [finalSt]
        have hinit_cli : (lookupCli ({ curSpec := spec, effectiveVersion := spec.version } : Internal.ParseState).cliOpts opt.name).reverse = [] := rfl
        rw [lookupCli_map_rev, hcli_st opt.name, hinit_cli, List.nil_append,
          lookupCli_cliOptsOfPhrases hprops_f.nodupNames phrases ho]
      cases hsc : (!loopSt.curSpec.subcommands.isEmpty) with
      | true =>
        have hspec_err : ∃ e : CmdLineError,
            (Internal.parseWithEnvSpecM ops spec args validators w).1 = .error e ∧
            (!e.message.isEmpty) = true ∧ OtherErrKind e.kind := by
          unfold Internal.parseWithEnvSpecM
          rw [isValidSpecTR_eq, hv]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpt_ok, finalSt, hsc]
          cases loopSt.rawPositionals.reverse with
          | nil =>
            exact ⟨_, rfl, nonEmpty_str_append_left (nonEmpty_str_append_left rfl), otherErrKind_missingArgument⟩
          | cons unexpected _ =>
            exact ⟨_, rfl, nonEmpty_str_append_left (nonEmpty_str_append_left rfl),
              otherErrKind_unexpectedArgument⟩
        obtain ⟨e, he_eq, hm, hk⟩ := hspec_err
        rw [he_eq]
        exact Or.inl ⟨hNoValidOfErr he_eq, hNoHelpOfPtOk hpt_ok, hNoVerOfPtOk hpt_ok, Or.inr ⟨hm, hk⟩⟩
      | false =>
        have hleaf : loopSt.curSpec.subcommands.isEmpty = true := by simpa using hsc
        have hro_val := hro_eq (loopSt.inheritedGlobals ++ loopSt.curSpec.options) finalSt.cliOpts
        rw [resolveOptions_congr_lookup hlkp_eq] at hro_val
        cases hres_opts : Model.resolveOptions (m := Id) getEnv (loopSt.inheritedGlobals ++ loopSt.curSpec.options)
            (Model.cliOptsOfPhrases (loopSt.inheritedGlobals ++ loopSt.curSpec.options) phrases) validators with
        | error e =>
          rw [hres_opts] at hro_val
          have he_eq : (Internal.parseWithEnvSpecM ops spec args validators w).1 = .error e := by
            unfold Internal.parseWithEnvSpecM
            rw [isValidSpecTR_eq, hv]
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpt_ok, finalSt, hleaf, Bind.bind, StateT.bind]
            cases hRunRo : Internal.resolveOptionsTR ops.getEnv (loopSt.inheritedGlobals ++ loopSt.curSpec.options)
                (loopSt.cliOpts.map (fun p => (p.1, p.2.reverse))) validators w with
            | mk roRes w1 =>
              dsimp only [finalSt] at hro_val
              rw [hRunRo] at hro_val; dsimp only at hro_val; subst hro_val; rfl
          rw [he_eq]
          exact Or.inl ⟨hNoValidOfErr he_eq, hNoHelpOfPtOk hpt_ok, hNoVerOfPtOk hpt_ok,
            resolveOptions_err_props hres_opts⟩
        | ok resolvedOpts =>
          rw [hres_opts] at hro_val
          have hpos_rev : finalSt.rawPositionals = phrases.flatMap Model.CliPhrase.posTokens := by
            dsimp only [finalSt]; rw [hpos_st, List.reverse_reverse]
          cases hres_args : Model.resolveArgs loopSt.curSpec.args (phrases.flatMap Model.CliPhrase.posTokens) validators with
          | error e =>
            have he_eq : (Internal.parseWithEnvSpecM ops spec args validators w).1 = .error e := by
              unfold Internal.parseWithEnvSpecM
              rw [isValidSpecTR_eq, hv]
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpt_ok, finalSt, hleaf, Bind.bind, StateT.bind]
              cases hRunRo : Internal.resolveOptionsTR ops.getEnv (loopSt.inheritedGlobals ++ loopSt.curSpec.options)
                  (loopSt.cliOpts.map (fun p => (p.1, p.2.reverse))) validators w with
              | mk roRes w1 =>
                dsimp only [finalSt] at hro_val hpos_rev
                rw [hRunRo] at hro_val; dsimp only at hro_val; subst hro_val
                dsimp only
                rw [resolveArgsTR_eq, hpos_rev, hres_args]; rfl
            rw [he_eq]
            exact Or.inl ⟨hNoValidOfErr he_eq, hNoHelpOfPtOk hpt_ok, hNoVerOfPtOk hpt_ok,
              Or.inr (resolveArgs_err_props hres_args)⟩
          | ok resolvedArgs =>
            let parsed : ParsedCmd :=
              { subcommandPath := loopSt.subPath
                options := resolvedOpts
                args := resolvedArgs
                rawPositionals := phrases.flatMap Model.CliPhrase.posTokens }
            have hok_eq : (Internal.parseWithEnvSpecM ops spec args validators w).1 = .ok parsed := by
              unfold Internal.parseWithEnvSpecM
              rw [isValidSpecTR_eq, hv]
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpt_ok, finalSt, hleaf, Bind.bind, StateT.bind]
              cases hRunRo : Internal.resolveOptionsTR ops.getEnv (loopSt.inheritedGlobals ++ loopSt.curSpec.options)
                  (loopSt.cliOpts.map (fun p => (p.1, p.2.reverse))) validators w with
              | mk roRes w1 =>
                dsimp only [finalSt] at hro_val hpos_rev
                rw [hRunRo] at hro_val; dsimp only at hro_val; subst hro_val
                dsimp only
                rw [resolveArgsTR_eq, hpos_rev, hres_args]; rfl
            rw [hok_eq]
            exact ⟨hv, loopSt.inheritedGlobals, loopSt.effectiveVersion, loopSt.curSpec,
              hpath_f, hleaf, phrases, hargs_eq, hchk_ok, hsub_st.symm, rfl, hres_opts, hres_args⟩
    · have he_eq : (Internal.parseWithEnvSpecM ops spec args validators w).1 = .error e := by
        unfold Internal.parseWithEnvSpecM
        rw [isValidSpecTR_eq, hv]
        simp [hpt_err, Pure.pure, StateT.pure]
      rw [he_eq]
      simp only [List.map_nil, List.flatten_nil, List.nil_append] at herr_cls
      rcases herr_cls with ⟨hk, hm, hhelp⟩ | ⟨hk, hm, hver⟩ | ⟨hm, hk⟩
      · exact Or.inr (Or.inl ⟨hk, hm, hhelp⟩)
      · exact Or.inr (Or.inr ⟨hk, hm, hver⟩)
      · refine Or.inl ⟨hNoValidOfErr he_eq, ?_, ?_, Or.inr ⟨hm, hk⟩⟩
        · intro hhelp
          obtain ⟨e_h, hh_err, hh_k⟩ := existsHelpInvocation_sound hv hhelp
          rw [hpt_err] at hh_err; injection hh_err with he_eh; subst he_eh
          exact hk.2.1 hh_k.1
        · intro hver
          obtain ⟨e_v, hv_err, hv_k⟩ := existsVersionInvocation_sound hv hver
          rw [hpt_err] at hv_err; injection hv_err with he_ev; subst he_ev
          exact hk.2.2.1 hv_k.1

end LeanSwe.CmdLine.Proofs

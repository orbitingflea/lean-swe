import Core.Assumptions
import LeanSwe.CmdLine.Interface
import LeanSwe.CmdLine.SpecTests
import LeanSwe.CmdLine.Proofs.ParserCore
namespace LeanSwe.CmdLine.Proofs
open Core LeanSwe.CmdLine LeanSwe.CmdLine.Proofs.Shared
private def exceptKindIn {α : Type} (P : CmdLineErrorKind → Prop) (r : Except CmdLineError α) : Prop :=
  match r with | .ok _ => True | .error e => P e.kind
private theorem exceptKindIn_bind {α β : Type} {P : CmdLineErrorKind → Prop} (r : Except CmdLineError α) (k : α → Except CmdLineError β) (hr : exceptKindIn P r) (hk : ∀ a, exceptKindIn P (k a)) : exceptKindIn P (r >>= k) := by cases r with | error _ => exact hr | ok a => exact hk a
private theorem exceptKindIn_mk {α : Type} {P : CmdLineErrorKind → Prop} {kd : CmdLineErrorKind} {msg : String} {tgt : Option String} (h : P kd) : exceptKindIn P (Except.error { kind := kd, message := msg, target := tgt } : Except CmdLineError α) := h
private theorem parseOptValue_kind {k : ValueKind} {s : String} : exceptKindIn (fun kd => kd = .invalidValue) (Model.parseOptValue k s) := by
  unfold Model.parseOptValue; cases k <;> dsimp only <;> first | trivial | (cases Model.parseBoolString s <;> trivial) | (cases Model.parseNatChars s.toList <;> trivial) | (cases Model.parseIntChars s.toList <;> trivial) | (split <;> trivial)
private theorem parseOptValueWith_error {k : ValueKind} {s : String} {v : CustomValidators} {e : CmdLineError} (h : Model.parseOptValueWith k s v = Except.error e) : e.kind = .invalidValue := by
  have hk : exceptKindIn (fun kd => kd = .invalidValue) (Model.parseOptValueWith k s v) := by
    unfold Model.parseOptValueWith; refine exceptKindIn_bind _ _ parseOptValue_kind fun _ => exceptKindIn_bind _ _ ?_ fun _ => trivial
    unfold Model.validateCustomValue; cases k <;> dsimp only <;> first | trivial | (cases v.find? _ with | none => trivial | some p => dsimp only; cases p.2 s <;> trivial)
  rw [h] at hk; exact hk
private theorem parseShortBundle_noEofIo (visibleOpts : List OptSpec) (shortHelp shortVersion : Bool) (rootName : String) (subPath : List String) (effVer : Option String) (curSpec : CommandSpec) (validators : CustomValidators) (cliOpts : List (String × List OptValue)) (cs : List Char) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) (Internal.parseShortBundle visibleOpts shortHelp shortVersion rootName subPath effVer curSpec validators cliOpts cs) := by
  induction cs generalizing cliOpts with | nil => simp [Internal.parseShortBundle, exceptKindIn] | cons c rest ih =>
    unfold Internal.parseShortBundle; dsimp only; split; · exact exceptKindIn_mk (by decide)
    · split; · cases effVer <;> exact exceptKindIn_mk (by decide)
      · cases visibleOpts.find? (fun o => o.short == some c) with
        | none => exact exceptKindIn_mk (by decide)
        | some opt =>
          dsimp only; split
          · exact ih _
          · split
            · dsimp only [bind, Except.bind]; rw [Shared.parseOptValueWithFast_eq]; cases hp : Model.parseOptValueWith opt.kind (String.ofList rest) validators with | error _ => exact exceptKindIn_mk (by rw [parseOptValueWith_error hp]; decide) | ok _ => trivial
            · trivial
private theorem stepToken_noEofIo (rootName : String) (validators : CustomValidators) (st : Internal.ParseState) (tok : String) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) (Internal.stepToken rootName validators st tok) := by
  unfold Internal.stepToken; cases st.pendingOpt with
  | some opt => dsimp only [bind, Except.bind]; rw [Shared.parseOptValueWithFast_eq]; cases hp : Model.parseOptValueWith opt.kind tok validators with | error _ => exact exceptKindIn_mk (by rw [parseOptValueWith_error hp]; decide) | ok _ => trivial
  | none =>
    dsimp only; by_cases hadd : st.afterDashDash
    · simp [hadd, exceptKindIn]
    · simp only [hadd, Bool.false_eq_true, ↓reduceIte]; by_cases hdd : tok == "--"; · simp [hdd, exceptKindIn]
      · simp only [hdd, Bool.false_eq_true, ↓reduceIte]; by_cases hhlp : tok == "--help"; · simp [hhlp]; exact exceptKindIn_mk (by decide)
        · simp only [hhlp, Bool.false_eq_true, ↓reduceIte]; by_cases hver : (tok == "--version" && st.effectiveVersion.isSome)
          · simp only [hver, ↓reduceIte]; cases st.effectiveVersion <;> exact exceptKindIn_mk (by decide)
          · simp only [hver, Bool.false_eq_true, ↓reduceIte]; split
            · split; · exact exceptKindIn_mk (by decide)
              · split; · exact exceptKindIn_mk (by decide)
                · cases Internal.lookupLongOpt (st.inheritedGlobals ++ st.curSpec.options) _ with | none => exact exceptKindIn_mk (by decide) | some p =>
                    dsimp only; split
                    · cases (Internal.splitFirstEq _).2 <;> first | exact exceptKindIn_mk (by decide) | trivial
                    · split
                      · cases (Internal.splitFirstEq _).2 with | none => trivial | some rawVal =>
                          dsimp only; cases hp : Model.parseOptValue .bool rawVal with
                          | error _ => have h := parseOptValue_kind (k := .bool) (s := rawVal); rw [hp] at h; exact exceptKindIn_mk (by rw [h]; decide)
                          | ok v => cases v <;> first | (dsimp only; split <;> first | exact exceptKindIn_mk (by decide) | trivial) | exact exceptKindIn_mk (by decide)
                      · cases (Internal.splitFirstEq _).2 with | none => trivial | some rawVal =>
                          dsimp only [bind, Except.bind]; rw [Shared.parseOptValueWithFast_eq]; cases hp : Model.parseOptValueWith p.1.kind rawVal validators with | error _ => exact exceptKindIn_mk (by rw [parseOptValueWith_error hp]; decide) | ok _ => trivial
            · dsimp only [bind, Except.bind]; rename_i c_s sr_s _ _; have hsb := parseShortBundle_noEofIo (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp st.curSpec.shortVersion rootName st.subPath st.effectiveVersion st.curSpec validators st.cliOpts (c_s :: sr_s)
              cases hsb_eq : Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options) st.curSpec.shortHelp st.curSpec.shortVersion rootName st.subPath st.effectiveVersion st.curSpec validators st.cliOpts (c_s :: sr_s) with | error _ => rw [hsb_eq] at hsb; exact hsb | ok _ => trivial
            · split
              · cases st.curSpec.subcommands.find? (fun s => s.name == tok) <;> first | trivial | exact exceptKindIn_mk (by decide)
              · trivial
private theorem parseTokensLoop_noEofIo (rootName : String) (validators : CustomValidators) (st : Internal.ParseState) (tokens : List String) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) (Internal.parseTokensLoop rootName validators st tokens) := by
  induction tokens generalizing st with
  | nil => trivial
  | cons tok rest ih => unfold Internal.parseTokensLoop; exact exceptKindIn_bind _ _ (stepToken_noEofIo rootName validators st tok) ih
private theorem parseTokens_noEofIo (rootName : String) (validators : CustomValidators) (st : Internal.ParseState) (tokens : List String) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) (Internal.parseTokens rootName validators st tokens) := by
  unfold Internal.parseTokens
  refine exceptKindIn_bind _ _ (parseTokensLoop_noEofIo rootName validators st tokens) fun finalSt => ?_
  cases finalSt.pendingOpt <;> first | trivial | exact exceptKindIn_mk (by decide)
private theorem resolveOptDefault_noEofIo (opt : OptSpec) (validators : CustomValidators) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) (Model.resolveOptDefault opt validators) := by
  unfold Model.resolveOptDefault
  cases opt.default with
  | some d =>
    dsimp only; cases hp : Model.parseOptValueWith opt.kind d validators with
    | error _ => exact exceptKindIn_mk (by rw [parseOptValueWith_error hp]; decide)
    | ok _ => trivial
  | none => dsimp only; split <;> first | exact exceptKindIn_mk (by decide) | (split <;> trivial)
private theorem resolveSingleOption_pureNoEnv_noEofIo (opt : OptSpec) (cliVals : List OptValue) (validators : CustomValidators) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) (Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt cliVals validators) := by
  unfold Model.resolveSingleOption; by_cases hcli : !cliVals.isEmpty
  · simp only [hcli, ↓reduceIte, pure]; split <;> first | exact exceptKindIn_mk (by decide) | trivial
  · simp only [hcli, Bool.false_eq_true, ↓reduceIte, pure, Bind.bind, Internal.pureNoEnvOps]; cases opt.envVar <;> exact resolveOptDefault_noEofIo opt validators
private theorem resolveOptions_pureNoEnv_noEofIo (visibleOpts : List OptSpec) (cliOpts : List (String × List OptValue)) (validators : CustomValidators) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) (Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv visibleOpts cliOpts validators) := by
  induction visibleOpts with
  | nil => simp [Model.resolveOptions, exceptKindIn, pure]
  | cons opt rest ih =>
    unfold Model.resolveOptions; dsimp only [bind, pure]
    have h1 := resolveSingleOption_pureNoEnv_noEofIo opt (match cliOpts.find? (fun p => p.1 == opt.name) with | some p => p.2 | none => []) validators
    cases hs : Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt (match cliOpts.find? (fun p => p.1 == opt.name) with | some p => p.2 | none => []) validators with
    | error _ => rw [hs] at h1; erw [hs]; exact h1
    | ok res? =>
      erw [hs]; dsimp only
      cases ht : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv rest cliOpts validators with
      | error _ => rw [ht] at ih; dsimp only; exact ih
      | ok _ => dsimp only; cases res? <;> trivial
private theorem resolveArgs_parseMany_noEofIo (arg : ArgSpec) (validators : CustomValidators) (xs : List String) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) (Model.resolveArgs.parseMany validators arg xs) := by
  induction xs with
  | nil => simp [Model.resolveArgs.parseMany, exceptKindIn]
  | cons s _ ih =>
    unfold Model.resolveArgs.parseMany; dsimp only [bind, pure, Except.bind, Except.pure]
    cases hp : Model.parseOptValueWith arg.kind s validators with
    | error _ => exact exceptKindIn_mk (by rw [parseOptValueWith_error hp]; decide)
    | ok _ => exact exceptKindIn_bind _ _ ih fun _ => trivial
private theorem resolveArgs_go_noEofIo (validators : CustomValidators) (argSpecs : List ArgSpec) (rawPos : List String) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) (Model.resolveArgs.go validators argSpecs rawPos) := by
  induction argSpecs generalizing rawPos with
  | nil => cases rawPos <;> first | trivial | exact exceptKindIn_mk (by decide)
  | cons arg restArgs ih =>
    unfold Model.resolveArgs.go; dsimp only [bind, pure, Except.bind, Except.pure]
    split
    · split
      · split
        · exact exceptKindIn_mk (by decide)
        · cases arg.default with
          | none => exact ih []
          | some d => dsimp only; cases hp : Model.parseOptValueWith arg.kind d validators with
            | error _ => (try rw [hp]); dsimp only [exceptKindIn]; rw [parseOptValueWith_error hp]; decide
            | ok _ => (try rw [hp]); cases hr : Model.resolveArgs.go validators restArgs [] with | error _ => have h := ih []; rw [hr] at h; exact h | ok _ => trivial
      · exact exceptKindIn_bind _ _ (resolveArgs_parseMany_noEofIo arg validators rawPos) fun _ => exceptKindIn_bind _ _ (ih []) fun _ => trivial
    · cases rawPos with
      | cons s remPos =>
        dsimp only; cases hp : Model.parseOptValueWith arg.kind s validators with
        | error _ => (try rw [hp]); dsimp only [exceptKindIn]; rw [parseOptValueWith_error hp]; decide
        | ok _ => (try rw [hp]); cases hr : Model.resolveArgs.go validators restArgs remPos with | error _ => have h := ih remPos; rw [hr] at h; exact h | ok _ => trivial
      | nil =>
        by_cases hreq : arg.required
        · simp only [hreq, ↓reduceIte]; exact exceptKindIn_mk (by decide)
        · simp only [hreq, Bool.false_eq_true, ↓reduceIte]
          cases arg.default with
          | none => exact ih []
          | some d => dsimp only; cases hp : Model.parseOptValueWith arg.kind d validators with
            | error _ => (try rw [hp]); dsimp only [exceptKindIn]; rw [parseOptValueWith_error hp]; decide
            | ok _ => (try rw [hp]); cases hr : Model.resolveArgs.go validators restArgs [] with | error _ => have h := ih []; rw [hr] at h; exact h | ok _ => trivial
private theorem parseWith_never_of (spec : CommandSpec) (args : List String) (validators : CustomValidators) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) (CmdLine.parseWith spec args validators) := by
  unfold CmdLine.parseWith defaultApi Internal.mkApiFromCapsM Internal.mkApiM Internal.parseWith; simp only [Shared.parseWithEnvM_eq_spec]; unfold Internal.parseWithEnvSpecM; dsimp only [pure, bind]
  split
  · exact exceptKindIn_mk (by decide)
  · have htok := parseTokens_noEofIo spec.name validators { curSpec := spec, effectiveVersion := spec.version } args
    cases hp : Internal.parseTokens spec.name validators { curSpec := spec, effectiveVersion := spec.version } args with
    | error _ => rw [hp] at htok; exact htok
    | ok finalState =>
      dsimp only; split
      · split <;> exact exceptKindIn_mk (by decide)
      · rw [resolveOptionsTR_id_eq, resolveArgsTR_eq]
        have hopts := resolveOptions_pureNoEnv_noEofIo (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators
        cases ho : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators with
        | error _ => rw [ho] at hopts; exact hopts
        | ok _ =>
          dsimp only; have hargs := resolveArgs_go_noEofIo validators finalState.curSpec.args finalState.rawPositionals; unfold Model.resolveArgs
          cases ha : Model.resolveArgs.go validators finalState.curSpec.args finalState.rawPositionals with
          | error _ => rw [ha] at hargs; exact hargs
          | ok _ => trivial
private theorem parseWith_never_kind {spec : CommandSpec} {args : List String} {validators : CustomValidators} {k : CmdLineErrorKind}
    (hk : k = .eof ∨ k = .ioError) : Core.NeverErrorKindPure CmdLineError.kind k (CmdLine.parseWith spec args validators) := by
  have h := parseWith_never_of spec args validators; unfold Core.NeverErrorKindPure
  cases hr : CmdLine.parseWith spec args validators with
  | ok _ => trivial
  | error _ => rw [hr] at h; rcases hk with rfl | rfl <;> first | exact h.1 | exact h.2
/-- Proof that `CmdLine.parse` never returns `.eof`. -/
theorem cmdline_parse_never_eof (spec : CommandSpec) (args : List String) : Core.NeverErrorKindPure CmdLineError.kind .eof (CmdLine.parse spec args) := parseWith_never_kind (Or.inl rfl)
/-- Proof that `CmdLine.parse` never returns `.ioError`. -/
theorem cmdline_parse_never_ioError (spec : CommandSpec) (args : List String) : Core.NeverErrorKindPure CmdLineError.kind .ioError (CmdLine.parse spec args) := parseWith_never_kind (Or.inr rfl)
/-- Proof that `CmdLine.parseWith` never returns `.eof`. -/
theorem cmdline_parseWith_never_eof (spec : CommandSpec) (args : List String) (validators : CustomValidators) : Core.NeverErrorKindPure CmdLineError.kind .eof (CmdLine.parseWith spec args validators) := parseWith_never_kind (Or.inl rfl)
/-- Proof that `CmdLine.parseWith` never returns `.ioError`. -/
theorem cmdline_parseWith_never_ioError (spec : CommandSpec) (args : List String) (validators : CustomValidators) : Core.NeverErrorKindPure CmdLineError.kind .ioError (CmdLine.parseWith spec args validators) := parseWith_never_kind (Or.inr rfl)
private def estOutCmdLineAllowed {α : Type} (P : CmdLineError → Prop) (out : EST.Out IO.Error IO.RealWorld (Except CmdLineError α)) : Prop :=
  match out with | EST.Out.error _ _ => True | EST.Out.ok (.ok _) _ => True | EST.Out.ok (.error e) _ => P e
private theorem io_bind_eq {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld) {a : α} {w' : Void IO.RealWorld} (h : act w = EST.Out.ok a w') : (act >>= k) w = k a w' := by change EST.bind act k w = k a w'; simp [EST.bind, h]
private theorem io_bind_err {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld) {ex : IO.Error} {w' : Void IO.RealWorld} (h : act w = EST.Out.error ex w') : (act >>= k) w = EST.Out.error ex w' := by change EST.bind act k w = EST.Out.error ex w'; simp [EST.bind, h]
private theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) : (pure a : IO α) w = EST.Out.ok a w := rfl
private theorem io_bind_allowed {α β : Type} (P : CmdLineError → Prop) (act : IO α) (k : α → IO (Except CmdLineError β)) (w : Void IO.RealWorld) (hk : ∀ a w', estOutCmdLineAllowed P (k a w')) : estOutCmdLineAllowed P ((act >>= k) w) := by
  cases ha : act w with | error _ w' => rw [io_bind_err _ _ w ha]; trivial | ok a w' => rw [io_bind_eq _ _ w ha]; exact hk a w'
private theorem baseIO_liftM_never_throws {α : Type} (act : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', (liftM act : IO α) w = EST.Out.ok a w' := by
  simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO]
  cases act w with
  | mk a s => exact ⟨a, s, rfl⟩

private theorem io_bind_full {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld) :
    (act >>= k) w =
      match act w with
      | EST.Out.ok a w' => k a w'
      | EST.Out.error ex w' => EST.Out.error ex w' := by
  change EST.bind act k w = _
  unfold EST.bind
  cases act w <;> rfl

private theorem mkRawOps_envvars_getEnv_never_throws
    (g : String → BaseIO (Option ByteArray)) (l : BaseIO (Array ByteArray))
    (key : String) (w : Void IO.RealWorld) :
    ∃ res w',
      (LeanSwe.EnvVars.Internal.mkApiM
        (LeanSwe.EnvVars.Raw.Internal.mkRawOps (m := IO) {
          getEnvBytes := fun k => liftM (g k)
          listEnvironBytes := liftM l
        })).getEnv key w = EST.Out.ok res w' := by
  dsimp only [LeanSwe.EnvVars.Internal.mkApiM, LeanSwe.EnvVars.Raw.Internal.mkRawOps]
  by_cases hk : LeanSwe.EnvVars.Internal.isValidKey key
  · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hpk : LeanSwe.EnvVars.Raw.Internal.isValidPosixKey key
    · simp only [hpk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [io_bind_full, io_bind_full]
      rcases baseIO_liftM_never_throws (g key) w with ⟨mb, w1, hG⟩
      rw [hG]
      cases mb with
      | none => exact ⟨.ok none, w1, rfl⟩
      | some bs =>
        dsimp only
        cases hutf : String.fromUTF8? bs with
        | some s => dsimp only; exact ⟨.ok (some s), w1, rfl⟩
        | none => dsimp only; exact ⟨_, w1, rfl⟩
    · simp only [hpk, Bool.not_false, ↓reduceIte]
      rw [io_bind_full, io_pure_eq]
      exact ⟨.ok none, w, rfl⟩
  · simp only [hk, Bool.not_false, ↓reduceIte]
    exact ⟨_, w, rfl⟩

private theorem envvars_getEnv_never_throws (key : String) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.EnvVars.getEnv key w = EST.Out.ok res w' := by
  unfold LeanSwe.EnvVars.getEnv LeanSwe.EnvVars.defaultApi
  apply mkRawOps_envvars_getEnv_never_throws

private theorem defaultOps_getEnv_noThrow_noEof (key : String) (w : Void IO.RealWorld) :
    (∃ v w', defaultOps.getEnv key w = EST.Out.ok (Except.ok v) w') ∨
      (∃ e w', defaultOps.getEnv key w = EST.Out.ok (Except.error e) w' ∧ e.kind ≠ .eof) := by
  rcases envvars_getEnv_never_throws key w with ⟨res, w', hr⟩
  unfold LeanSwe.EnvVars.getEnv at hr
  unfold defaultOps Internal.mkCliOpsFromCapsM SysBridge.mkFilesCliOpsM SysBridge.mapEnvVarsGet
  dsimp only
  rw [io_bind_eq _ _ w hr]
  cases res with
  | ok v => exact Or.inl ⟨v, w', io_pure_eq _ _⟩
  | error err =>
    exact Or.inr ⟨Model.mapEnvVarsErrorModel err,
      w', io_pure_eq _ _, fun hc => by cases hc⟩
private theorem resolveSingleOption_defaultOps_noEof (opt : OptSpec) (cliVals : List OptValue) (validators : CustomValidators) (w : Void IO.RealWorld) :
    ∃ r w', Model.resolveSingleOption defaultOps.getEnv opt cliVals validators w = EST.Out.ok r w' ∧ exceptKindIn (fun kd => kd ≠ .eof) r := by
  unfold Model.resolveSingleOption; by_cases hcli : !cliVals.isEmpty
  · simp only [hcli, ↓reduceIte]; split <;> first | exact ⟨_, w, io_pure_eq _ _, exceptKindIn_mk (by decide)⟩ | exact ⟨_, w, io_pure_eq _ _, trivial⟩
  · simp only [hcli, Bool.false_eq_true, ↓reduceIte]
    have defNoEof : exceptKindIn (fun kd => kd ≠ .eof) (Model.resolveOptDefault opt validators) := by have h := resolveOptDefault_noEofIo opt validators; cases hr : Model.resolveOptDefault opt validators <;> first | trivial | (rw [hr] at h; exact h.1)
    cases opt.envVar with | none => exact ⟨_, w, io_pure_eq _ _, defNoEof⟩ | some envKey =>
      dsimp only; rcases defaultOps_getEnv_noThrow_noEof envKey w with ⟨v, w', hv⟩ | ⟨e, w', he, hne⟩
      · cases v with | none => rw [io_bind_eq _ _ w hv]; exact ⟨_, w', io_pure_eq _ _, defNoEof⟩ | some s =>
          by_cases hs : s = ""
          · subst hs; rw [io_bind_eq _ _ w hv]; exact ⟨_, w', io_pure_eq _ _, defNoEof⟩
          · have hm : (match (Except.ok (some s) : Except CmdLineError (Option String)) with | .error e => (pure (.error e) : IO (Except CmdLineError (Option (List OptValue)))) | .ok none => pure (Model.resolveOptDefault opt validators) | .ok (some "") => pure (Model.resolveOptDefault opt validators) | .ok (some x) => match Model.parseOptValueWith opt.kind x validators with | .error e => pure (.error { e with target := some opt.name }) | .ok v => if opt.repeatable && opt.kind == ValueKind.bool && v == OptValue.bool false then pure (.ok none) else pure (.ok (some [v]))) = (match Model.parseOptValueWith opt.kind s validators with | .error e => (pure (.error { e with target := some opt.name }) : IO (Except CmdLineError (Option (List OptValue)))) | .ok v => if opt.repeatable && opt.kind == ValueKind.bool && v == OptValue.bool false then pure (.ok none) else pure (.ok (some [v]))) := by
              split <;> first | (rename_i h; cases h; done) | (rename_i _ h; cases h; exact absurd rfl hs) | (rename_i _ _ h; injection h with h1; injection h1 with h2; subst h2; rfl)
            cases hp : Model.parseOptValueWith opt.kind s validators with
            | error e => refine ⟨.error { e with target := some opt.name }, w', (io_bind_eq _ _ w hv).trans ((congrFun hm w').trans ?_), ?_⟩ <;> first | (rw [hp]; exact io_pure_eq _ _) | (dsimp only [exceptKindIn]; rw [parseOptValueWith_error hp]; decide)
            | ok v =>
              by_cases hrep : (opt.repeatable && opt.kind == ValueKind.bool && v == OptValue.bool false) = true
              · refine ⟨.ok none, w', (io_bind_eq _ _ w hv).trans ((congrFun hm w').trans ?_), trivial⟩; rw [hp]; simp [hrep, io_pure_eq]
              · refine ⟨.ok (some [v]), w', (io_bind_eq _ _ w hv).trans ((congrFun hm w').trans ?_), trivial⟩; rw [hp]; simp [hrep, io_pure_eq]
      · rw [io_bind_eq _ _ w he]; exact ⟨_, w', io_pure_eq _ _, hne⟩
private theorem resolveOptionsTR_defaultOps_noEof (visibleOpts : List OptSpec) (cliOpts : List (String × List OptValue)) (validators : CustomValidators) (w : Void IO.RealWorld) :
    ∃ r w', Internal.resolveOptionsTR defaultOps.getEnv visibleOpts cliOpts validators w = EST.Out.ok r w' ∧ exceptKindIn (fun kd => kd ≠ .eof) r := by
  unfold Internal.resolveOptionsTR; suffices h : ∀ accRev w, ∃ r w', Internal.resolveOptionsTR.go defaultOps.getEnv cliOpts validators visibleOpts accRev w = EST.Out.ok r w' ∧ exceptKindIn (fun kd => kd ≠ .eof) r from h [] w
  induction visibleOpts with | nil => intro accRev w; exact ⟨_, w, io_pure_eq _ _, trivial⟩ | cons opt _ ih =>
    intro accRev w; unfold Internal.resolveOptionsTR.go; simp only [Shared.resolveSingleOptionFast_eq]
    rcases resolveSingleOption_defaultOps_noEof opt (match cliOpts.find? (fun p => p.1 == opt.name) with | some p => p.2 | none => []) validators w with ⟨r1, w1, hr1, hk1⟩
    erw [io_bind_eq _ _ w hr1]; cases r1 with | error _ => exact ⟨_, w1, io_pure_eq _ _, hk1⟩ | ok res? => dsimp only; cases res? <;> exact ih _ w1
/-- Proof that `CmdLine.parseWithEnv` never returns `.eof`. -/
theorem cmdline_parseWithEnv_never_eof (spec : CommandSpec) (args : List String) (validators : CustomValidators) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .eof (CmdLine.parseWithEnv spec args validators) w := by
  unfold Core.NeverErrorKindIO CmdLine.parseWithEnv defaultApi Internal.mkApiFromCapsM Internal.mkApiM
  rw [show Internal.mkCliOpsFromCapsM { files := LeanSwe.LinuxSyscall.Files.defaultOps, env := LeanSwe.EnvVars.defaultApi } = defaultOps from rfl]
  simp only [Shared.parseWithEnvM_eq_spec]; unfold Internal.parseWithEnvSpecM; dsimp only
  rw [Shared.isValidSpecTR_eq]; cases hv : Model.isValidSpec spec
  · simp only [Bool.not_false, ↓reduceIte, io_pure_eq]; decide
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; have htok := parseTokens_noEofIo spec.name validators { curSpec := spec, effectiveVersion := spec.version } args
    cases hp : Internal.parseTokens spec.name validators { curSpec := spec, effectiveVersion := spec.version } args with
    | error _ => rw [hp] at htok; dsimp only; rw [io_pure_eq]; exact htok.1
    | ok finalState =>
      dsimp only; by_cases hsub : finalState.curSpec.subcommands.isEmpty
      · simp only [hsub, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases resolveOptionsTR_defaultOps_noEof (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators w with ⟨ro, w1, hro, hko⟩
        rw [io_bind_eq _ _ w hro]
        cases ro with
        | error _ => dsimp only; rw [io_pure_eq]; exact hko
        | ok _ =>
          dsimp only; have hargs := resolveArgs_go_noEofIo validators finalState.curSpec.args finalState.rawPositionals; rw [resolveArgsTR_eq]
          cases ha : Model.resolveArgs finalState.curSpec.args finalState.rawPositionals validators with
          | error _ => change Model.resolveArgs.go _ _ _ = _ at ha; rw [ha] at hargs; dsimp only; rw [io_pure_eq]; exact hargs.1
          | ok _ => dsimp only; rw [io_pure_eq]; trivial
      · simp only [hsub, Bool.not_false, ↓reduceIte]; cases finalState.rawPositionals.isEmpty <;> simp [io_pure_eq]
private theorem findSubcommandPath_kind (spec : CommandSpec) (path : List String) :
    exceptKindIn (fun kd => kd = .unknownSubcommand) (Model.findSubcommandPath spec path) := by
  unfold Model.findSubcommandPath
  have hgo : ∀ (globals : List OptSpec) (ver : Option String) (cur : CommandSpec) (p : List String), exceptKindIn (fun kd => kd = .unknownSubcommand) (Model.findSubcommandPath.go globals ver cur p) := by
    intro globals ver cur p; induction p generalizing globals ver cur with
    | nil => simp [Model.findSubcommandPath.go, exceptKindIn]
    | cons name _ ih => unfold Model.findSubcommandPath.go; cases cur.subcommands.find? (fun s => s.name == name) with | none => rfl | some sub => exact ih _ _ sub
  exact hgo [] none spec path
private theorem renderHelp_never_of (rootSpec : CommandSpec) (subcommandPath : List String) (k : CmdLineErrorKind) (hk1 : k ≠ .invalidSpec) (hk2 : k ≠ .unknownSubcommand) :
    Core.NeverErrorKindPure CmdLineError.kind k (CmdLine.renderHelp rootSpec subcommandPath) := by
  have hk : exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .unknownSubcommand) (CmdLine.renderHelp rootSpec subcommandPath) := by
    unfold CmdLine.renderHelp defaultApi Internal.mkApiFromCapsM Internal.mkApiM Internal.renderHelp; dsimp only
    split
    · exact Or.inl rfl
    · refine exceptKindIn_bind _ _ ?_ fun _ => trivial
      have h := findSubcommandPath_kind rootSpec subcommandPath
      rw [Shared.findSubcommandPathTR_eq]
      cases hf : Model.findSubcommandPath rootSpec subcommandPath <;> first | (rw [hf] at h; exact Or.inr h) | trivial
  unfold Core.NeverErrorKindPure
  cases hr : CmdLine.renderHelp rootSpec subcommandPath with
  | ok _ => trivial
  | error _ => rw [hr] at hk; rcases hk with he | he <;> first | exact fun heq => hk1 (heq ▸ he) | exact fun heq => hk2 (heq ▸ he)
/-- Proof that `CmdLine.renderHelp` never returns `.helpRequested`. -/
theorem cmdline_renderHelp_never_helpRequested (rootSpec : CommandSpec) (subcommandPath : List String) : Core.NeverErrorKindPure CmdLineError.kind .helpRequested (CmdLine.renderHelp rootSpec subcommandPath) := renderHelp_never_of rootSpec subcommandPath .helpRequested (by decide) (by decide)
/-- Proof that `CmdLine.renderHelp` never returns `.versionRequested`. -/
theorem cmdline_renderHelp_never_versionRequested (rootSpec : CommandSpec) (subcommandPath : List String) : Core.NeverErrorKindPure CmdLineError.kind .versionRequested (CmdLine.renderHelp rootSpec subcommandPath) := renderHelp_never_of rootSpec subcommandPath .versionRequested (by decide) (by decide)
/-- Proof that `CmdLine.renderHelp` never returns `.unknownOption`. -/
theorem cmdline_renderHelp_never_unknownOption (rootSpec : CommandSpec) (subcommandPath : List String) : Core.NeverErrorKindPure CmdLineError.kind .unknownOption (CmdLine.renderHelp rootSpec subcommandPath) := renderHelp_never_of rootSpec subcommandPath .unknownOption (by decide) (by decide)
/-- Proof that `CmdLine.renderHelp` never returns `.missingOption`. -/
theorem cmdline_renderHelp_never_missingOption (rootSpec : CommandSpec) (subcommandPath : List String) : Core.NeverErrorKindPure CmdLineError.kind .missingOption (CmdLine.renderHelp rootSpec subcommandPath) := renderHelp_never_of rootSpec subcommandPath .missingOption (by decide) (by decide)
/-- Proof that `CmdLine.renderHelp` never returns `.missingArgument`. -/
theorem cmdline_renderHelp_never_missingArgument (rootSpec : CommandSpec) (subcommandPath : List String) : Core.NeverErrorKindPure CmdLineError.kind .missingArgument (CmdLine.renderHelp rootSpec subcommandPath) := renderHelp_never_of rootSpec subcommandPath .missingArgument (by decide) (by decide)
/-- Proof that `CmdLine.renderHelp` never returns `.unexpectedArgument`. -/
theorem cmdline_renderHelp_never_unexpectedArgument (rootSpec : CommandSpec) (subcommandPath : List String) : Core.NeverErrorKindPure CmdLineError.kind .unexpectedArgument (CmdLine.renderHelp rootSpec subcommandPath) := renderHelp_never_of rootSpec subcommandPath .unexpectedArgument (by decide) (by decide)
/-- Proof that `CmdLine.renderHelp` never returns `.invalidValue`. -/
theorem cmdline_renderHelp_never_invalidValue (rootSpec : CommandSpec) (subcommandPath : List String) : Core.NeverErrorKindPure CmdLineError.kind .invalidValue (CmdLine.renderHelp rootSpec subcommandPath) := renderHelp_never_of rootSpec subcommandPath .invalidValue (by decide) (by decide)
/-- Proof that `CmdLine.renderHelp` never returns `.eof`. -/
theorem cmdline_renderHelp_never_eof (rootSpec : CommandSpec) (subcommandPath : List String) : Core.NeverErrorKindPure CmdLineError.kind .eof (CmdLine.renderHelp rootSpec subcommandPath) := renderHelp_never_of rootSpec subcommandPath .eof (by decide) (by decide)
/-- Proof that `CmdLine.renderHelp` never returns `.ioError`. -/
theorem cmdline_renderHelp_never_ioError (rootSpec : CommandSpec) (subcommandPath : List String) : Core.NeverErrorKindPure CmdLineError.kind .ioError (CmdLine.renderHelp rootSpec subcommandPath) := renderHelp_never_of rootSpec subcommandPath .ioError (by decide) (by decide)
private theorem renderValueList_kind (opt : OptSpec) (vs : List OptValue) :
    exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .invalidValue) (Model.renderSingleOpt.renderValueList opt vs) := by
  induction vs with
  | nil => simp [Model.renderSingleOpt.renderValueList, exceptKindIn]
  | cons _ rest ih =>
    unfold Model.renderSingleOpt.renderValueList
    split
    · exact exceptKindIn_mk (Or.inr rfl)
    · cases opt.long with
      | some _ => dsimp only; split <;> cases hr : Model.renderSingleOpt.renderValueList opt rest <;> first | (rw [hr] at ih; exact ih) | trivial
      | none => cases opt.short with | none => exact exceptKindIn_mk (Or.inl rfl) | some _ => dsimp only; split <;> cases hr : Model.renderSingleOpt.renderValueList opt rest <;> first | (rw [hr] at ih; exact ih) | trivial
private theorem renderSingleOpt_kind (opt : OptSpec) (vals : List OptValue) :
    exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .invalidValue) (Model.renderSingleOpt opt vals) := by
  unfold Model.renderSingleOpt
  split
  · trivial
  · split
    · cases vals with
      | nil => exact exceptKindIn_mk (Or.inr rfl)
      | cons v rest =>
        cases rest with
        | cons _ _ => split <;> first | (rename_i h; cases h) | exact exceptKindIn_mk (Or.inr rfl)
        | nil =>
          cases v with
          | bool b =>
            cases b
            · cases opt.long <;> first | trivial | (dsimp only; cases opt.default <;> first | (simp [exceptKindIn]; done) | (dsimp only; split <;> first | exact exceptKindIn_mk (Or.inr rfl) | trivial))
            · cases opt.long <;> first | (cases opt.short <;> first | exact exceptKindIn_mk (Or.inl rfl) | trivial) | trivial
          | _ => exact exceptKindIn_mk (Or.inr rfl)
    · exact renderValueList_kind opt vals
private theorem renderArgs_never_of (spec : CommandSpec) (parsed : ParsedCmd) (k : CmdLineErrorKind)
    (hk1 : k ≠ .invalidSpec) (hk2 : k ≠ .unknownSubcommand) (hk3 : k ≠ .missingArgument) (hk4 : k ≠ .invalidValue) :
    Core.NeverErrorKindPure CmdLineError.kind k (CmdLine.renderArgs spec parsed) := by
  have hk : exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .unknownSubcommand ∨ kd = .missingArgument ∨ kd = .invalidValue) (CmdLine.renderArgs spec parsed) := by
    unfold CmdLine.renderArgs defaultApi Internal.mkApiFromCapsM Internal.mkApiM; dsimp only
    rw [Shared.renderArgsTR_eq]; unfold Model.renderArgs; dsimp only [bind, pure, Except.bind, Except.pure]
    split
    · exact exceptKindIn_mk (Or.inl rfl)
    · have h := findSubcommandPath_kind spec parsed.subcommandPath
      cases hf : Model.findSubcommandPath spec parsed.subcommandPath with
      | error _ => rw [hf] at h; exact Or.inr (Or.inl h)
      | ok p =>
        dsimp only; split
        · exact exceptKindIn_mk (Or.inr (Or.inr (Or.inl rfl)))
        · have hro : ∀ opts, exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .unknownSubcommand ∨ kd = .missingArgument ∨ kd = .invalidValue) (Model.renderArgs.renderOpts parsed opts) := by
            intro opts; induction opts with
            | nil => simp [Model.renderArgs.renderOpts, exceptKindIn]
            | cons o _ ih =>
              unfold Model.renderArgs.renderOpts
              have h1 := renderSingleOpt_kind o (match parsed.options.find? (fun p => p.1 == o.name) with | some p => p.2 | none => [])
              have h1' : exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .unknownSubcommand ∨ kd = .missingArgument ∨ kd = .invalidValue) (Model.renderSingleOpt o (match parsed.options.find? (fun p => p.1 == o.name) with | some p => p.2 | none => [])) := by
                cases hm : Model.renderSingleOpt o _ <;> first | trivial | (rw [hm] at h1; dsimp only [exceptKindIn] at h1 ⊢; rcases h1 with a | b <;> first | exact Or.inl a | exact Or.inr (Or.inr (Or.inr b)))
              exact exceptKindIn_bind _ _ h1' fun _ => exceptKindIn_bind _ _ ih fun _ => trivial
          exact exceptKindIn_bind _ _ (hro (p.1 ++ p.2.2.options)) fun _ => trivial
  unfold Core.NeverErrorKindPure
  cases hr : CmdLine.renderArgs spec parsed with
  | ok _ => trivial
  | error _ => rw [hr] at hk; rcases hk with h | h | h | h <;> first | exact fun heq => hk1 (heq ▸ h) | exact fun heq => hk2 (heq ▸ h) | exact fun heq => hk3 (heq ▸ h) | exact fun heq => hk4 (heq ▸ h)
/-- Proof that `CmdLine.renderArgs` never returns `.helpRequested`. -/
theorem cmdline_renderArgs_never_helpRequested (spec : CommandSpec) (parsed : ParsedCmd) : Core.NeverErrorKindPure CmdLineError.kind .helpRequested (CmdLine.renderArgs spec parsed) := renderArgs_never_of spec parsed .helpRequested (by decide) (by decide) (by decide) (by decide)
/-- Proof that `CmdLine.renderArgs` never returns `.versionRequested`. -/
theorem cmdline_renderArgs_never_versionRequested (spec : CommandSpec) (parsed : ParsedCmd) : Core.NeverErrorKindPure CmdLineError.kind .versionRequested (CmdLine.renderArgs spec parsed) := renderArgs_never_of spec parsed .versionRequested (by decide) (by decide) (by decide) (by decide)
/-- Proof that `CmdLine.renderArgs` never returns `.unknownOption`. -/
theorem cmdline_renderArgs_never_unknownOption (spec : CommandSpec) (parsed : ParsedCmd) : Core.NeverErrorKindPure CmdLineError.kind .unknownOption (CmdLine.renderArgs spec parsed) := renderArgs_never_of spec parsed .unknownOption (by decide) (by decide) (by decide) (by decide)
/-- Proof that `CmdLine.renderArgs` never returns `.missingOption`. -/
theorem cmdline_renderArgs_never_missingOption (spec : CommandSpec) (parsed : ParsedCmd) : Core.NeverErrorKindPure CmdLineError.kind .missingOption (CmdLine.renderArgs spec parsed) := renderArgs_never_of spec parsed .missingOption (by decide) (by decide) (by decide) (by decide)
/-- Proof that `CmdLine.renderArgs` never returns `.unexpectedArgument`. -/
theorem cmdline_renderArgs_never_unexpectedArgument (spec : CommandSpec) (parsed : ParsedCmd) : Core.NeverErrorKindPure CmdLineError.kind .unexpectedArgument (CmdLine.renderArgs spec parsed) := renderArgs_never_of spec parsed .unexpectedArgument (by decide) (by decide) (by decide) (by decide)
/-- Proof that `CmdLine.renderArgs` never returns `.eof`. -/
theorem cmdline_renderArgs_never_eof (spec : CommandSpec) (parsed : ParsedCmd) : Core.NeverErrorKindPure CmdLineError.kind .eof (CmdLine.renderArgs spec parsed) := renderArgs_never_of spec parsed .eof (by decide) (by decide) (by decide) (by decide)
/-- Proof that `CmdLine.renderArgs` never returns `.ioError`. -/
theorem cmdline_renderArgs_never_ioError (spec : CommandSpec) (parsed : ParsedCmd) : Core.NeverErrorKindPure CmdLineError.kind .ioError (CmdLine.renderArgs spec parsed) := renderArgs_never_of spec parsed .ioError (by decide) (by decide) (by decide) (by decide)
private def estOutNoThrowAllowed {α : Type} (P : CmdLineError → Prop) (out : EST.Out IO.Error IO.RealWorld (Except CmdLineError α)) : Prop :=
  match out with | EST.Out.error _ _ => False | EST.Out.ok (.ok _) _ => True | EST.Out.ok (.error e) _ => P e
private theorem catchStdioM_bind_allowed {α β : Type} (P : CmdLineError → Prop)
    (hIo : ∀ msg, P (Model.mkStdioIoError msg))
    (act : IO α) (k : Except CmdLineError α → IO (Except CmdLineError β))
    (w : Void IO.RealWorld)
    (hk : ∀ a w', estOutNoThrowAllowed P (k (.ok a) w'))
    (he : ∀ e, P e → ∀ w', estOutNoThrowAllowed P (k (.error e) w')) :
    estOutNoThrowAllowed P ((SysBridge.catchStdioM act >>= k) w) := by
  have hCatch : (∃ a w', SysBridge.catchStdioM act w = EST.Out.ok (.ok a) w') ∨
      (∃ msg w', SysBridge.catchStdioM act w = EST.Out.ok (.error (Model.mkStdioIoError msg)) w') := by
    unfold SysBridge.catchStdioM
    have hMap : (Except.ok <$> act : IO (Except CmdLineError α)) = (act >>= fun a => pure (Except.ok a)) := rfl
    rw [hMap]
    change (∃ a w', EST.tryCatch (act >>= fun a => pure (Except.ok a)) (fun err => pure (Except.error (Model.mkStdioIoError err.toString))) w = EST.Out.ok (Except.ok a) w') ∨
      (∃ msg w', EST.tryCatch (act >>= fun a => pure (Except.ok a)) (fun err => pure (Except.error (Model.mkStdioIoError err.toString))) w = EST.Out.ok (Except.error (Model.mkStdioIoError msg)) w')
    unfold EST.tryCatch
    cases ha : act w with
    | error err w' =>
      have hm : (act >>= fun a => pure (Except.ok a : Except CmdLineError α)) w = EST.Out.error err w' :=
        io_bind_err act _ w ha
      exact Or.inr ⟨err.toString, w', by erw [hm]; exact io_pure_eq _ _⟩
    | ok a w' =>
      have hm : (act >>= fun a => pure (Except.ok a : Except CmdLineError α)) w = EST.Out.ok (Except.ok a) w' := by
        rw [io_bind_eq act _ w ha]; exact io_pure_eq _ _
      exact Or.inl ⟨a, w', by erw [hm]⟩
  rcases hCatch with ⟨a, w', hOk⟩ | ⟨msg, w', hErr⟩
  · rw [io_bind_eq _ _ w hOk]; exact hk a w'
  · rw [io_bind_eq _ _ w hErr]; exact he _ (hIo msg) w'
private theorem checked_promptLine_allowed (ops : CliOps) (prompt : String) (default : Option String)
    (k : CmdLineErrorKind) (hk1 : k ≠ .eof) (hk2 : k ≠ .ioError) (w : Void IO.RealWorld) :
    estOutNoThrowAllowed (fun e => e.kind ≠ k) (SysBridge.promptLineCheckedM ops prompt default w) := by
  unfold SysBridge.promptLineCheckedM
  refine catchStdioM_bind_allowed _ (fun _ => hk2.symm) _ _ w
    (fun _ w1 => catchStdioM_bind_allowed _ (fun _ => hk2.symm) _ _ w1
      (fun line? w2 => ?_) (fun e he w2 => by dsimp only; rw [io_pure_eq]; exact he))
    (fun e he w1 => by dsimp only; rw [io_pure_eq]; exact he)
  cases line? with
  | none => dsimp only; rw [io_pure_eq]; exact hk1.symm
  | some _ => dsimp only; split <;> first | (cases default <;> dsimp only <;> rw [io_pure_eq] <;> trivial) | (rw [io_pure_eq]; trivial)
private theorem checked_confirm_allowed (ops : CliOps) (prompt : String) (default : Option Bool) (maxAttempts : Nat)
    (k : CmdLineErrorKind) (hk1 : k ≠ .eof) (hk2 : k ≠ .invalidValue) (hk3 : k ≠ .ioError) (w : Void IO.RealWorld) :
    estOutNoThrowAllowed (fun e => e.kind ≠ k) (SysBridge.confirmCheckedM ops prompt default maxAttempts w) := by
  induction maxAttempts generalizing w with
  | zero => unfold SysBridge.confirmCheckedM; rw [io_pure_eq]; exact hk2.symm
  | succ n ih =>
    unfold SysBridge.confirmCheckedM
    refine catchStdioM_bind_allowed _ (fun _ => hk3.symm) _ _ w
      (fun _ w1 => catchStdioM_bind_allowed _ (fun _ => hk3.symm) _ _ w1
        (fun line? w2 => ?_) (fun e he w2 => by dsimp only; rw [io_pure_eq]; exact he))
      (fun e he w1 => by dsimp only; rw [io_pure_eq]; exact he)
    cases line? with
    | none => dsimp only; rw [io_pure_eq]; exact hk1.symm
    | some _ =>
      dsimp only; split
      · cases default with
        | some _ => dsimp only; rw [io_pure_eq]; trivial
        | none =>
          cases n with
          | zero => dsimp only; rw [io_pure_eq]; exact hk2.symm
          | succ _ =>
            exact catchStdioM_bind_allowed _ (fun _ => hk3.symm) _ _ w2
              (fun _ w3 => ih w3) (fun e he w3 => by dsimp only; rw [io_pure_eq]; exact he)
      · split
        · rw [io_pure_eq]; trivial
        · split
          · rw [io_pure_eq]; trivial
          · cases n with
            | zero => dsimp only; rw [io_pure_eq]; exact hk2.symm
            | succ _ =>
              exact catchStdioM_bind_allowed _ (fun _ => hk3.symm) _ _ w2
                (fun _ w3 => ih w3) (fun e he w3 => by dsimp only; rw [io_pure_eq]; exact he)
private theorem promptLine_never_of (prompt : String) (default : Option String) (k : CmdLineErrorKind) (hk1 : k ≠ .eof) (hk2 : k ≠ .ioError) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind k (CmdLine.promptLine prompt default) w := by
  unfold Core.NeverErrorKindIO CmdLine.promptLine defaultApi Internal.mkApiFromCapsM; dsimp only
  rw [show Internal.mkCliOpsFromCapsM { files := LeanSwe.LinuxSyscall.Files.defaultOps, env := LeanSwe.EnvVars.defaultApi } = defaultOps from rfl]
  have h := checked_promptLine_allowed defaultOps prompt default k hk1 hk2 w
  cases hr : SysBridge.promptLineCheckedM defaultOps prompt default w with
  | error _ _ => rw [hr] at h; exact h
  | ok res _ => rw [hr] at h; cases res with | ok _ => trivial | error _ => exact h
private theorem confirm_never_of (prompt : String) (default : Option Bool) (maxAttempts : Nat) (k : CmdLineErrorKind) (hk1 : k ≠ .eof) (hk2 : k ≠ .invalidValue) (hk3 : k ≠ .ioError) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind k (CmdLine.confirm prompt default maxAttempts) w := by
  unfold Core.NeverErrorKindIO CmdLine.confirm defaultApi Internal.mkApiFromCapsM; dsimp only
  rw [show Internal.mkCliOpsFromCapsM { files := LeanSwe.LinuxSyscall.Files.defaultOps, env := LeanSwe.EnvVars.defaultApi } = defaultOps from rfl]
  have h := checked_confirm_allowed defaultOps prompt default maxAttempts k hk1 hk2 hk3 w
  cases hr : SysBridge.confirmCheckedM defaultOps prompt default maxAttempts w with
  | error _ _ => rw [hr] at h; exact h
  | ok res _ => rw [hr] at h; cases res with | ok _ => trivial | error _ => exact h
/-- Proof that `CmdLine.promptLine` never returns `.helpRequested`. -/
theorem cmdline_promptLine_never_helpRequested (prompt : String) (default : Option String) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .helpRequested (CmdLine.promptLine prompt default) w := promptLine_never_of prompt default .helpRequested (by decide) (by decide) w
/-- Proof that `CmdLine.promptLine` never returns `.versionRequested`. -/
theorem cmdline_promptLine_never_versionRequested (prompt : String) (default : Option String) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .versionRequested (CmdLine.promptLine prompt default) w := promptLine_never_of prompt default .versionRequested (by decide) (by decide) w
/-- Proof that `CmdLine.promptLine` never returns `.unknownOption`. -/
theorem cmdline_promptLine_never_unknownOption (prompt : String) (default : Option String) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .unknownOption (CmdLine.promptLine prompt default) w := promptLine_never_of prompt default .unknownOption (by decide) (by decide) w
/-- Proof that `CmdLine.promptLine` never returns `.missingOption`. -/
theorem cmdline_promptLine_never_missingOption (prompt : String) (default : Option String) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .missingOption (CmdLine.promptLine prompt default) w := promptLine_never_of prompt default .missingOption (by decide) (by decide) w
/-- Proof that `CmdLine.promptLine` never returns `.missingArgument`. -/
theorem cmdline_promptLine_never_missingArgument (prompt : String) (default : Option String) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .missingArgument (CmdLine.promptLine prompt default) w := promptLine_never_of prompt default .missingArgument (by decide) (by decide) w
/-- Proof that `CmdLine.promptLine` never returns `.unexpectedArgument`. -/
theorem cmdline_promptLine_never_unexpectedArgument (prompt : String) (default : Option String) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .unexpectedArgument (CmdLine.promptLine prompt default) w := promptLine_never_of prompt default .unexpectedArgument (by decide) (by decide) w
/-- Proof that `CmdLine.promptLine` never returns `.invalidValue`. -/
theorem cmdline_promptLine_never_invalidValue (prompt : String) (default : Option String) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .invalidValue (CmdLine.promptLine prompt default) w := promptLine_never_of prompt default .invalidValue (by decide) (by decide) w
/-- Proof that `CmdLine.promptLine` never returns `.unknownSubcommand`. -/
theorem cmdline_promptLine_never_unknownSubcommand (prompt : String) (default : Option String) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .unknownSubcommand (CmdLine.promptLine prompt default) w := promptLine_never_of prompt default .unknownSubcommand (by decide) (by decide) w
/-- Proof that `CmdLine.promptLine` never returns `.invalidSpec`. -/
theorem cmdline_promptLine_never_invalidSpec (prompt : String) (default : Option String) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .invalidSpec (CmdLine.promptLine prompt default) w := promptLine_never_of prompt default .invalidSpec (by decide) (by decide) w
/-- Proof that `CmdLine.confirm` never returns `.helpRequested`. -/
theorem cmdline_confirm_never_helpRequested (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .helpRequested (CmdLine.confirm prompt default maxAttempts) w := confirm_never_of prompt default maxAttempts .helpRequested (by decide) (by decide) (by decide) w
/-- Proof that `CmdLine.confirm` never returns `.versionRequested`. -/
theorem cmdline_confirm_never_versionRequested (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .versionRequested (CmdLine.confirm prompt default maxAttempts) w := confirm_never_of prompt default maxAttempts .versionRequested (by decide) (by decide) (by decide) w
/-- Proof that `CmdLine.confirm` never returns `.unknownOption`. -/
theorem cmdline_confirm_never_unknownOption (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .unknownOption (CmdLine.confirm prompt default maxAttempts) w := confirm_never_of prompt default maxAttempts .unknownOption (by decide) (by decide) (by decide) w
/-- Proof that `CmdLine.confirm` never returns `.missingOption`. -/
theorem cmdline_confirm_never_missingOption (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .missingOption (CmdLine.confirm prompt default maxAttempts) w := confirm_never_of prompt default maxAttempts .missingOption (by decide) (by decide) (by decide) w
/-- Proof that `CmdLine.confirm` never returns `.missingArgument`. -/
theorem cmdline_confirm_never_missingArgument (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .missingArgument (CmdLine.confirm prompt default maxAttempts) w := confirm_never_of prompt default maxAttempts .missingArgument (by decide) (by decide) (by decide) w
/-- Proof that `CmdLine.confirm` never returns `.unexpectedArgument`. -/
theorem cmdline_confirm_never_unexpectedArgument (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .unexpectedArgument (CmdLine.confirm prompt default maxAttempts) w := confirm_never_of prompt default maxAttempts .unexpectedArgument (by decide) (by decide) (by decide) w
/-- Proof that `CmdLine.confirm` never returns `.unknownSubcommand`. -/
theorem cmdline_confirm_never_unknownSubcommand (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .unknownSubcommand (CmdLine.confirm prompt default maxAttempts) w := confirm_never_of prompt default maxAttempts .unknownSubcommand (by decide) (by decide) (by decide) w
/-- Proof that `CmdLine.confirm` never returns `.invalidSpec`. -/
theorem cmdline_confirm_never_invalidSpec (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) : Core.NeverErrorKindIO CmdLineError.kind .invalidSpec (CmdLine.confirm prompt default maxAttempts) w := confirm_never_of prompt default maxAttempts .invalidSpec (by decide) (by decide) (by decide) w
/-- `Model.stripTrailingNewlineModel` equals `Internal.stripTrailingNewline` definitionally. -/
theorem stripTrailingNewlineModel_eq (s : String) : Model.stripTrailingNewlineModel s = Internal.stripTrailingNewline s := rfl
/-- `Model.decodeUtf8LossyLean` maps empty bytes to the empty string. -/
theorem decodeUtf8LossyLean_empty : Model.decodeUtf8LossyLean ByteArray.empty = "" := rfl
/-- `Model.validateUtf8OneWidth` decodes any ASCII byte (`< 0x80`) as a 1-byte codepoint. -/
theorem validateUtf8OneWidth_ascii (bs : ByteArray) (i : Nat) (hi : i < bs.size) (ha : bs[i] < 0x80) :
    Model.validateUtf8OneWidth bs i = some (bs[i].toNat, 1) := by unfold Model.validateUtf8OneWidth; simp [hi, ha]
/-- `Model.stepDefaultGetEnv` always rejects invalid environment keys with `.ioError`. -/
theorem stepDefaultGetEnv_invalidKey (w : Model.StdioWorld) (key : String) (hk : Model.isValidEnvKey key = false) :
    ∃ e, Model.stepDefaultGetEnv w key = .error e ∧ e.kind = .ioError ∧ e.target = some key := by unfold Model.stepDefaultGetEnv; simp [hk]
/-- `Model.stepChannelWrite` on an empty string is a total no-op for any stream backend. -/
theorem stepChannelWrite_empty (ch : Model.StdioChannelState) :
    Model.stepChannelWrite ch "" = (.returned (), ch) := by
  unfold Model.stepChannelWrite; simp
/-- On an empty clean `StdioWorld`, `Model.stepPromptLine` agrees with `mockCliOps` EOF error. -/
theorem stepPromptLine_eof_agrees_mock (prompt : String) (default : Option String) :
    (Model.stepPromptLine { stdin := { backing := .nullDev }, stdout := { backing := .nullDev } } prompt default).1 =
      ((Internal.promptLine mockCliOps prompt default).run {}).1 := by
  unfold Model.stepPromptLine Model.stepDefaultWriteOut Model.stepChannelWrite Model.updateWorldErrno Model.stepDefaultReadLine Model.stepRawGetLine Internal.promptLine mockCliOps
  cases prompt.isEmpty <;> rfl
/-- For `maxAttempts = 0`, `Model.stepConfirm` agrees with `mockCliOps`. -/
theorem stepConfirm_zero_agrees_mock (w : Model.StdioWorld) (prompt : String) (default : Option Bool) (st : CliMockState) :
    (Model.stepConfirm w prompt default 0).1 = ((Internal.confirm mockCliOps prompt default 0).run st).1 := rfl
/-- `SysBridge.stdioEintrFuel` agrees with `Model.stdioEintrRetryLimit` (`64`). -/
theorem stdioEintrFuel_eq_modelLimit : SysBridge.stdioEintrFuel = Model.stdioEintrRetryLimit := rfl
/-- On an open empty blocking pipe, a transient `EINTR` burst within `Model.stdioEintrRetryLimit` (`≤ 64`) is absorbed rather than throwing `.interrupted`. -/
theorem stepDefaultReadLine_pipe_transient_absorbed (count : Nat) (h : count ≤ Model.stdioEintrRetryLimit) :
    (Model.stepDefaultReadLine {
      stdin := { backing := .pipe ByteArray.empty false false false 65536, pendingInterrupt := .transient count } }).1 =
      .threwIo .blocked := by
  unfold Model.stepDefaultReadLine Model.stepRawGetLine Model.PendingInterrupt.exhaustsRetries
  have hgt : ¬(Model.stdioEintrRetryLimit < count) := by omega
  have hsp : Model.splitLineBytes ByteArray.empty = none := by decide
  simp [hsp, hgt]
/-- On an open empty blocking pipe, an `EINTR` burst exceeding `Model.stdioEintrRetryLimit` (`> 64`) throws `.interrupted`. -/
theorem stepDefaultReadLine_pipe_transient_exhaust (count : Nat) (h : count > Model.stdioEintrRetryLimit) :
    (Model.stepDefaultReadLine {
      stdin := { backing := .pipe ByteArray.empty false false false 65536, pendingInterrupt := .transient count } }).1 =
      .threwIo .interrupted := by
  unfold Model.stepDefaultReadLine Model.stepRawGetLine Model.PendingInterrupt.exhaustsRetries
  have hsp : Model.splitLineBytes ByteArray.empty = none := by decide
  simp [hsp, h]
/-- On an open empty blocking pipe, a `.repeating` `EINTR` stream throws `.interrupted`. -/
theorem stepDefaultReadLine_pipe_repeating_interrupted :
    (Model.stepDefaultReadLine {
      stdin := { backing := .pipe ByteArray.empty false false false 65536, pendingInterrupt := .repeating } }).1 =
      .threwIo .interrupted := by
  unfold Model.stepDefaultReadLine Model.stepRawGetLine Model.PendingInterrupt.exhaustsRetries
  have hsp : Model.splitLineBytes ByteArray.empty = none := by decide
  simp [hsp]
end LeanSwe.CmdLine.Proofs

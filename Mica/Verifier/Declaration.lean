-- SUMMARY: One declaration at a time: elaborate it, declare the spec functions it defines, check it, and bind what it defines for the declarations after it.
import Mica.SourceTinyML.Typing
import Mica.SourceTinyML.Erasure
import Mica.Verifier.PrimitiveLaws
import Mica.Verifier.RelationalEncoding
import Mica.Verifier.Intrinsic
import Mica.Verifier.BoundedQuantifier
import Mica.Verifier.Expressions
import Mica.Verifier.Ghost

open Verifier (State)

/-!
# Declarations

The verifier handles a program one declaration at a time. `Decl.declare`
elaborates a declaration against the environment of the declarations before it,
and declares the spec functions it defines and the bounded quantifiers its
specifications lift. `Decl.check` checks the typed declaration in the scope of
the values before it, and binds what it defines. `Decl.declareAndCheck` does
both.

Each declaration extends the world: it adds type declarations and spec symbols.
The scope carries over (`Scope.supportedBy_mono`): its types are well formed in
the world it was built in, so they mean the same in the larger one
(`ValHasType.agreeOn`).
-/

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]
open Verifier.RelationalEncoding (FunCtx PrimEncodings encode)
open Verifier.RelationalEncoding.Skolemize (DefVal)

/-! ## Ghost Declarations

A `[@@ghost]` declaration is a lemma. Its body sees only its own parameters, the
specification functions, and the ghost functions already declared: a name the
program binds is not in scope there. A recursive occurrence resolves under a
rank, and a recursive call must lower it.
-/

section GhostDeclarations

open Typed
open Verifier (Scope)

/-- The scope of a ghost declaration's body: the ghost functions, then the
    parameters. A name the program binds is not in scope there. -/
private def ghostBodyScope (Gf : GhostFunctions) (argNames : List String)
    (argVars : List Decl.Const) (argTys : List TinyML.Typ)
    (ghost : List (String × TinyML.Typ)) (ghostVars : List Decl.Const) : Scope :=
  (⟨Gf, [], [], TinyML.TyCtx.empty⟩ : Scope).bindParameters argNames argVars argTys ghost ghostVars

/-- The rank is a constant assumed equal to the measure at the declaration's own
    arguments. The measure must be well-formed in the parameter scope, so that a
    call can read it at its own arguments instead. -/
private def GhostFunctions.Guard.declare (Δ_spec : Signature) (measure : Typed.Measure)
    (names : List String) (terms : List (Term .value)) : VerifM GhostFunctions.Guard := do
  match measure.term.checkWf (Δ_spec.declVars (Spec.argVars names)) with
  | .error msg => VerifM.fatal msg
  | .ok () => do
    let m := measure.term.subst (Spec.argSubst Subst.id names terms)
    let Δ ← VerifM.decls
    match m.checkWf Δ with
    | .error msg => VerifM.fatal msg
    | .ok () => do
      let rv ← VerifM.define (some "rank") m
      pure ⟨measure, .const (.uninterpreted rv.name .int)⟩

/-- A recursive declaration is callable from its own body, under the rank its
    measure gives its own arguments. -/
private def ValDecl.ghostSelf (Δ_spec : Signature) (Gf : GhostFunctions) (self : Binder)
    (decreases : Option Typed.Measure) (ty : TinyML.Typ) (s : Spec TinyML.Typ)
    (argVars ghostVars : List Decl.Const) : VerifM GhostFunctions :=
  match self.name, decreases with
  | none, _ => pure Gf
  | some g, none =>
    VerifM.fatal s!"a recursive ghost declaration needs a [@@decreases] measure: {g}"
  | some g, some measure => do
    let terms := (argVars ++ ghostVars).map fun c => Term.const (.uninterpreted c.name .value)
    let guard ← GhostFunctions.Guard.declare Δ_spec measure s.allArgs terms
    pure ((g, ⟨ty, some guard⟩) :: Gf)

/-- Prove a specification by checking a function body as ghost code, and return
    the entry that makes the function callable from ghost code.

    A recursive declaration with no `[@@decreases]` measure is rejected: there is
    no rank to lower, so its self entry would be inconsistent. The entry keeps
    the arrow the body was checked at, so a call at a different instantiation of
    a polymorphic declaration fails the call's type check. -/
def ValDecl.prove (env : Verifier.Env) (Gf : GhostFunctions) (f : TinyML.Var) (self : Binder) (args : List Binder)
    (retTy : TinyML.Typ) (body : Expr) (s : Spec TinyML.Typ)
    (decreases : Option Typed.Measure) : SeqM (TinyML.Var × GhostFunctions.Entry) :=
  match extractArgNames args s.args with
  | .error msg => SeqM.fatal msg
  | .ok argNames =>
  let argTys := args.map Binder.WithTypeVars.ty
  let ty : TinyML.Typ := .arrow argTys retTy (some s)
  match TinyML.Typ.checkWf env.signature env.typeDeclarations ty with
  | .error msg => SeqM.fatal msg
  | .ok () => do
    SeqM.check do
      VerifM.persist
      Spec.implement env.signature argTys s fun argVars ghostVars => do
        let Gf' ← ValDecl.ghostSelf env.signature Gf self decreases ty s argVars ghostVars
        env.lemmas.assumeInstance self.name argVars
        let se ← compileGhostExpr env
          (ghostBodyScope Gf' argNames argVars argTys s.ghost ghostVars) body
        VerifM.expectEq "fix: body type does not match the return type" body.ty retTy
        pure se
    pure (f, ⟨ty, none⟩)

/-- Check a ghost declaration against the specification it was written with. -/
def ValDecl.checkGhost (env : Verifier.Env) (Gf : GhostFunctions) (d : Typed.ValDecl) :
    SeqM (TinyML.Var × GhostFunctions.Entry) :=
  match d.name.name, d.body with
  | none, _ => SeqM.fatal "a ghost declaration must be named"
  | some f, .fix self args retTy (some s) body =>
      ValDecl.prove env Gf f self args retTy body s d.decreases
  | some _, _ => SeqM.fatal "a ghost declaration must be a specified function"

/-- `$` is not an identifier character, so no name in the source collides. -/
private def fnResultName : String := "$result"

/-- What the body of a `[@@fn ghost]` declaration must prove: the spec-level
    function is defined at the argument, and its value is the one the body
    returns. The precondition is empty, so a call proves nothing. -/
def Spec.ofRelation (rel : SpecFn) (arg : String) : Spec TinyML.Typ :=
  { args := [arg], ghost := [],
    pred := .ret ⟨fnResultName,
      .assert (SpecFn.isDefined rel (.var .value arg))
        (.assert (.eq .value (.var .value fnResultName) (SpecFn.call rel (.var .value arg)))
          (.ret ()))⟩ }

/-- Make a spec-level function callable from ghost code, with its own body as
    the proof. A declaration without the `ghost` payload gets no entry. -/
def ValDecl.checkGhostFn (env : Verifier.Env) (Gf : GhostFunctions) (d : Typed.ValDecl) : SeqM GhostFunctions :=
  match d.relation with
  | some ⟨rel, true, _⟩ =>
    match d.name.name, d.body with
    | some f, .fix self [⟨some x, xty⟩] retTy _ body => do
      let entry ← ValDecl.prove env Gf f self [⟨some x, xty⟩] retTy body
        (Spec.ofRelation rel x) d.decreases
      pure [entry]
    | _, _ => SeqM.fatal
        s!"[@@fn ghost] requires a named function of one named argument: {rel}"
  | _ => pure []

/-- The unfolding function an opaque declaration publishes: its withheld fact,
    at its own argument type. -/
def ValDecl.publish (env : Verifier.Env) (d : Typed.ValDecl) :
    SeqM GhostFunctions :=
  match d.relation with
  | some r =>
    match r.transparency with
    | .transparent => pure []
    | .opaque =>
      match env.lemmas.ofDeclaration d.name.name, d.name.ty with
      | some l, .arrow [ty] _ _ =>
        match l.publish env.signature r.unfoldName ty with
        | .ok entry => do
          SeqM.ofExcept (TinyML.Typ.checkWf env.signature env.typeDeclarations entry.2.ty)
          pure [entry]
        | .error msg => SeqM.fatal msg
      | _, _ => SeqM.fatal
          s!"[@@opaque] requires a unary function that withholds its equation: {r.name}"
  | none => pure []

/-- The ghost entries a declaration contributes: the function `[@@fn ghost]`
    makes callable, and the unfolding function `[@@opaque]` publishes. -/
def ValDecl.ghostEntries (env : Verifier.Env) (Gf : GhostFunctions) (d : Typed.ValDecl) :
    SeqM GhostFunctions := do
  let fn ← ValDecl.checkGhostFn env Gf d
  let unf ← ValDecl.publish env d
  pure (fn ++ unf)

/-- The body's scope holds its parameters and nothing else, so its typing
    invariant comes entirely from the arguments the specification relates. -/
private theorem ValDecl.checkGhostBody_correct (env : Verifier.Env) (W : TinyML.World)
    (henv : env.wf W) (Gf : GhostFunctions)
    (s : Spec TinyML.Typ) (argTys : List TinyML.Typ) (retTy : TinyML.Typ) (body : Expr)
    (argNames : List String) (vs gs : List Runtime.Val) (Φ : Runtime.Val → iProp)
    (f : Option TinyML.Var)
    {argVars ghostVars : List Decl.Const} {st' : State} {ρ' : Env} {Q : iProp}
    (hag : W.agrees st'.decls ρ')
    (hGf : GhostFunctions.wellTyped W st'.decls ρ' Gf)
    (hlen_args : argNames.length = argTys.length)
    (hargVars_mem : ∀ v ∈ argVars, v ∈ st'.decls.consts)
    (hargVars_sort : ∀ v ∈ argVars, v.sort = .value)
    (hargVars_lookup : List.Forall₂ (fun av val => ρ'.consts .value av.name = val) argVars vs)
    (hghostVars_mem : ∀ v ∈ ghostVars, v ∈ st'.decls.consts)
    (hghostVars_sort : ∀ v ∈ ghostVars, v.sort = .value)
    (hghostVars_lookup : List.Forall₂ (fun gv val => ρ'.consts .value gv.name = val) ghostVars gs)
    (hbody_eval : VerifM.eval
        (do
          env.lemmas.assumeInstance f argVars
          let se ← compileGhostExpr env
            (ghostBodyScope Gf argNames argVars argTys s.ghost ghostVars) body
          VerifM.expectEq "fix: body type does not match the return type" body.ty retTy
          pure se)
        st' ρ'
        (fun result st'' ρ'' => ∀ X, result.wfIn st''.decls →
          st''.sl W ρ'' ∗ Q ∗
            ((TinyML.ValHasType W (result.eval ρ'') retTy -∗ Φ (result.eval ρ'')) -∗ X) ⊢ X)) :
    st'.sl W ρ' ∗ TinyML.ValsHaveTypes W vs argTys ∗
      TinyML.ValsHaveTypes W gs (s.ghost.map Prod.snd) ∗ Q ⊢ |==> ∃ v, Φ v := by
  obtain ⟨φs, hbody_eval⟩ := Lemmas.assumeInstance_correct henv.world henv.lemmas hag
    hargVars_mem hargVars_sort (VerifM.eval_bind hbody_eval)
  -- `sl` does not use the assertions, so `st₀.sl` is `st'.sl`.
  set st₀ : State := { st' with asserts := φs ++ st'.asserts }
  have hcompile := VerifM.eval_bind hbody_eval
  iintro ⟨Howns, #Hvals, #Hgvals, HQ⟩
  ihave %hlen_vals := TinyML.ValsHaveTypes.length_eq $$ Hvals
  ihave %hlen_gvals := TinyML.ValsHaveTypes.length_eq $$ Hgvals
  have hlen_av := hargVars_lookup.length_eq
  have hlen_gv := hghostVars_lookup.length_eq
  simp only [List.length_map] at hlen_gvals
  have hS := (Scope.wfIn_ghostFns (Γ := TinyML.TyCtx.empty) (γg := Runtime.Subst.id)
    (γ := Runtime.Subst.id) hag hGf).bindParameters (names := argNames) (tys := argTys)
    (ghost := s.ghost) (by omega) (by omega) (by omega) hargVars_mem
    hargVars_sort hargVars_lookup hghostVars_mem hghostVars_sort hghostVars_lookup
  have hbody := compileGhostExpr_correct body env W _ _ _ (st := st₀) (R := Q) (Φ := Φ) henv hS
    (VerifM.eval.decls_grow ρ' hcompile) (by
      intro v st'' ρ'' t hΨ ht_wf ht_eval
      obtain ⟨_, _, hΨ⟩ := hΨ
      obtain ⟨hsub, hΨ⟩ := VerifM.eval_bind_expectEq hΨ
      have hΨ' := VerifM.eval_ret hΨ
      rw [← ht_eval]
      refine (show st''.sl W ρ'' ∗ TinyML.ValHasType W (t.eval ρ'') body.ty ∗ Q ⊢
          st''.sl W ρ'' ∗ Q ∗
            ((TinyML.ValHasType W (t.eval ρ'') retTy -∗ Φ (t.eval ρ'')) -∗
              Φ (t.eval ρ'')) from ?_).trans (hΨ' _ ht_wf)
      iintro ⟨Howns', Hty, HQ'⟩
      iframe Howns' HQ'
      iintro Hwand
      iapply Hwand
      rw [← hsub]
      iexact Hty)
  iapply hbody
  isplitl [Howns]
  · iapply (show st'.sl W ρ' ⊢ st₀.sl W ρ' from .rfl)
    iexact Howns
  isplitr [HQ]
  · iapply (Scope.typed_bindParameters (by omega) hlen_av (by omega)
      hlen_gv)
    isplitl []
    · iapply Scope.typed_ghostFns
    · iframe # ∗
  · iexact HQ

omit [MicaGS HasLC.hasLC Sig] in
private theorem constTerms_eval {ρ : Env} :
    ∀ {vars : List Decl.Const} {vals : List Runtime.Val},
      List.Forall₂ (fun av val => ρ.consts .value av.name = val) vars vals →
      Term.evalList ρ (vars.map fun c => Term.const (.uninterpreted c.name .value)) vals
  | [], _, h => by cases h; exact .nil
  | a :: rest, _, h => by
    cases h with
    | cons hhead htail =>
      exact .cons (by simpa [Term.eval, Const.eval] using hhead) (constTerms_eval htail)

omit [MicaGS HasLC.hasLC Sig] in
/-- Argument constants keep their values as the verifier state grows. -/
private theorem constLookups_agreeOn {Δ : Signature} {ρ ρ' : Env}
    (hagree : Env.agreeOn Δ ρ ρ') :
    ∀ {vars : List Decl.Const} {vals : List Runtime.Val},
      (∀ v ∈ vars, v ∈ Δ.consts) → (∀ v ∈ vars, v.sort = .value) →
      List.Forall₂ (fun av val => ρ.consts .value av.name = val) vars vals →
      List.Forall₂ (fun av val => ρ'.consts .value av.name = val) vars vals
  | [], _, _, _, h => by cases h; exact .nil
  | a :: rest, _, hmem, hsort, h => by
    cases h with
    | cons hhead htail =>
      refine .cons ?_ (constLookups_agreeOn hagree
        (fun c hc => hmem c (.tail _ hc)) (fun c hc => hsort c (.tail _ hc)) htail)
      have hc := hagree.consts a (hmem a (.head _))
      rw [hsort a (.head _)] at hc
      rw [← hc]; exact hhead

/-- One rank of a ghost declaration's guarantee. `bodyGf` installs the ghost
    functions the body may call, which is where the recursive occurrence comes
    from. -/
private theorem ValDecl.checkGhostRank_correct (env : Verifier.Env) (W : TinyML.World)
    (henv : env.wf W) (argTys : List TinyML.Typ) (retTy : TinyML.Typ) (s : Spec TinyML.Typ) (body : Expr)
    (argNames : List String)
    (μ : List Runtime.Val → List Runtime.Val → Nat) (k : Nat)
    (bodyGf : List Decl.Const → List Decl.Const → VerifM GhostFunctions) (f : Option TinyML.Var)
    (hswf : s.wfIn W.Δ_spec) (hslen : s.args.length = argTys.length)
    (hlen_args : argNames.length = argTys.length)
    {st : State} {ρ : Env} (hag : W.agrees st.decls ρ) (howns : st.owns = [])
    (himpl : VerifM.eval (Spec.implement W.Δ_spec argTys s (fun argVars ghostVars => do
          let Gf' ← bodyGf argVars ghostVars
          env.lemmas.assumeInstance f argVars
          let se ← compileGhostExpr env
            (ghostBodyScope Gf' argNames argVars argTys s.ghost ghostVars) body
          VerifM.expectEq "fix: body type does not match the return type" body.ty retTy
          pure se)) st ρ (fun _ _ _ => True))
    (hbodyGf : ∀ (vs gs : List Runtime.Val) (argVars ghostVars : List Decl.Const)
        (st' : State) (ρ' : Env) (Ψ : GhostFunctions → State → Env → Prop),
      st.decls.Subset st'.decls → Env.agreeOn st.decls ρ ρ' →
      (∀ v ∈ argVars, v ∈ st'.decls.consts) → (∀ v ∈ argVars, v.sort = .value) →
      List.Forall₂ (fun av val => ρ'.consts .value av.name = val) argVars vs →
      (∀ v ∈ ghostVars, v ∈ st'.decls.consts) → (∀ v ∈ ghostVars, v.sort = .value) →
      List.Forall₂ (fun gv val => ρ'.consts .value gv.name = val) ghostVars gs →
      vs.length = argTys.length → gs.length = s.ghost.length → μ vs gs < k →
      VerifM.eval (bodyGf argVars ghostVars) st' ρ' Ψ →
      ∃ Gf' st'' ρ'', st'.decls.Subset st''.decls ∧ Env.agreeOn st'.decls ρ' ρ'' ∧
        (st'.sl W ρ' ⊢ st''.sl W ρ'') ∧ GhostFunctions.wellTyped W st''.decls ρ'' Gf' ∧
        Ψ Gf' st'' ρ'') :
    ⊢ Spec.isGhostPrecondForAt W (TinyML.ValHasType W) argTys retTy s μ k := by
  unfold Spec.isGhostPrecondForAt
  istart
  imodintro
  iintro %ρ_call %Φ %vs %gs %hagree_call %hlen_vs %hlen_gs %hrank #Hvals #Hgvals Hpred
  ihave Hwand := Spec.implement_correct W argTys retTy s _ st ρ vs gs Φ
    iprop(TinyML.ValsHaveTypes W vs argTys -∗
      TinyML.ValsHaveTypes W gs (s.ghost.map Prod.snd) -∗ |==> ∃ v, Φ v)
    hslen (by omega) hswf henv.world hag himpl
    (fun argVars ghostVars st' ρ' Q hst_sub hρ_agree hargVars_mem hargVars_sort hargVars_lookup
        hghostVars_mem hghostVars_sort hghostVars_lookup hbody_eval => by
      obtain ⟨Gf', st'', ρ'', hst_sub', hρ_agree', hsl_step, hGf', hrest⟩ :=
        hbodyGf vs gs argVars ghostVars st' ρ' _ hst_sub hρ_agree
          hargVars_mem hargVars_sort hargVars_lookup
          hghostVars_mem hghostVars_sort hghostVars_lookup hlen_vs hlen_gs hrank
          (VerifM.eval_bind hbody_eval)
      iintro ⟨Hsl, HQ⟩ Htyped Hgtyped
      iapply (ValDecl.checkGhostBody_correct env W henv Gf' s argTys retTy body argNames vs gs Φ
        f (hag.step (hst_sub.trans hst_sub') (Env.agreeOn_trans hρ_agree
          (Env.agreeOn_mono hst_sub hρ_agree')))
        hGf' hlen_args
        (fun v hv => hst_sub'.consts v (hargVars_mem v hv)) hargVars_sort
        (constLookups_agreeOn hρ_agree' hargVars_mem hargVars_sort hargVars_lookup)
        (fun v hv => hst_sub'.consts v (hghostVars_mem v hv)) hghostVars_sort
        (constLookups_agreeOn hρ_agree' hghostVars_mem hghostVars_sort hghostVars_lookup)
        hrest)
      isplitl [Hsl]
      · iapply hsl_step
        iexact Hsl
      · isplitl [Htyped]
        · iexact Htyped
        · isplitl [Hgtyped]
          · iexact Hgtyped
          · iexact HQ) $$ [Hpred]
  · isplitl []
    · simp [State.sl, howns]
      iempintro
    · isplitl []
      · iexact Hvals
      · isplitl []
        · iexact Hgvals
        · have hlen_call : s.allArgs.length ≤ (vs ++ gs).length := by
            simp [Spec.allArgs]; omega
          iapply (PredTrans.apply_agreeOn (TinyML.ValHasType W)
            (ρ := Spec.argsEnv ρ_call s.allArgs (vs ++ gs))
            (ρ' := Spec.argsEnv W.ρ_spec s.allArgs (vs ++ gs)) hswf
            (Spec.argsEnv_agreeOn (Δ := W.Δ_spec) (ρ₁ := ρ_call) (ρ₂ := W.ρ_spec)
              (Env.agreeOn_symm hagree_call) s.allArgs (vs ++ gs) hlen_call))
          iexact Hpred
  ispecialize Hwand $$ [Hvals]
  · iexact Hvals
  ispecialize Hwand $$ [Hgvals]
  · iexact Hgvals
  iexact Hwand

/-- The recursion is justified by strong induction on the rank the declaration's
    measure gives its arguments. -/
theorem ValDecl.prove_correct (env : Verifier.Env) (W : TinyML.World) (henv : env.wf W)
    (Gf : GhostFunctions) (f : TinyML.Var) (self : Binder) (args : List Binder)
    (retTy : TinyML.Typ) (body : Expr) (s : Spec TinyML.Typ)
    (decreases : Option Typed.Measure)
    {st : State} {ρ : Env} (hag : W.agrees st.decls ρ)
    (hGf : GhostFunctions.wellTyped W st.decls ρ Gf)
    {Q : (TinyML.Var × GhostFunctions.Entry) → State → Env → Prop}
    (heval : SeqM.eval (ValDecl.prove env Gf f self args retTy body s decreases) st ρ Q) :
    ∃ entry, GhostFunctions.wfIn W.Δ_spec W.Θ [entry] ∧ GhostFunctions.wellTyped W st.decls ρ [entry] ∧
      Q entry st ρ := by
  obtain ⟨reg, Θ, Δ, ls, fns, lfs, gls⟩ := env
  obtain ⟨-, -, -, rfl, rfl, -, -, -⟩ := id henv
  simp only [ValDecl.prove] at heval
  cases hext : extractArgNames args s.args with
    | error msg => simp only [hext] at heval; exact (SeqM.eval_fatal heval).elim
    | ok argNames =>
    simp only [hext] at heval
    cases hcheck : TinyML.Typ.checkWf W.Δ_spec W.Θ
        (.arrow (args.map Binder.WithTypeVars.ty) retTy (some s)) with
    | error msg => simp only [hcheck] at heval; exact (SeqM.eval_fatal heval).elim
    | ok u =>
    cases u
    simp only [hcheck] at heval
    obtain ⟨hargNames_len, hargs_len, _⟩ := extractArgNames_spec hext
    have htywf := TinyML.Typ.checkWf_ok _ hcheck
    have hswf : s.wfIn W.Δ_spec := by cases htywf; assumption
    have hslen : s.args.length = (args.map Binder.WithTypeVars.ty).length := by
      simpa using hargs_len.symm
    have hlen_args : argNames.length = (args.map Binder.WithTypeVars.ty).length := by
      simpa using hargNames_len.trans hargs_len.symm
    obtain ⟨himpl_seq, hcont⟩ := SeqM.eval_check (SeqM.eval_bind heval)
    have himpl := VerifM.eval_persist (VerifM.eval_bind himpl_seq)
    have hag' : W.agrees (State.persist st).decls ρ := hag
    have hGf' : GhostFunctions.wellTyped W (State.persist st).decls ρ Gf := hGf
    refine ⟨(f, ⟨.arrow (args.map Binder.WithTypeVars.ty) retTy (some s), none⟩),
      fun p hp => by cases List.mem_singleton.mp hp; exact ⟨rfl, htywf⟩, ?_,
      SeqM.eval_ret hcont⟩
    intro η f' argTys' retTy' s' guard' hlookup
    by_cases hf : f' = f
    · subst hf
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq,
        GhostFunctions.Entry.mk.injEq] at hlookup
      obtain ⟨hty, hguard⟩ := hlookup
      cases hty; cases hguard
      have hpersist_owns : (State.persist st).owns = [] := rfl
      cases hself : self.name with
      | none =>
        refine Spec.isGhostPrecondFor.induction_eta (fun _ _ => 0) ?_ η
        intro k η' _
        refine ValDecl.checkGhostRank_correct _ { W with eta := η' } (henv.eta η') _ retTy s body
          argNames _ k _ self.name hswf hslen hlen_args (hag'.eta η') hpersist_owns himpl ?_
        intro vs gs argVars ghostVars st₁ ρ₁ Ψ hst_sub hρ_agree _ _ _ _ _ _ _ _ _ hev
        simp only [ValDecl.ghostSelf, hself] at hev
        exact ⟨_, st₁, ρ₁, Signature.Subset.refl _, Env.agreeOn_refl, .rfl,
          GhostFunctions.wellTyped.eta (hGf'.step hst_sub hρ_agree (VerifM.eval.wf hev).namesDisjoint),
          VerifM.eval_ret hev⟩
      | some g =>
        cases hdec : decreases with
        | none =>
          refine Spec.isGhostPrecondFor.induction_eta (fun _ _ => 0) ?_ η
          intro k η' _
          refine ValDecl.checkGhostRank_correct _ { W with eta := η' } (henv.eta η') _ retTy s body
            argNames _ k _ self.name hswf hslen hlen_args (hag'.eta η') hpersist_owns himpl ?_
          intro vs gs argVars ghostVars st₁ ρ₁ Ψ _ _ _ _ _ _ _ _ _ _ _ hev
          simp only [ValDecl.ghostSelf, hself, hdec] at hev
          exact (VerifM.eval_fatal hev).elim
        | some measure =>
          refine Spec.isGhostPrecondFor.induction_eta (measure.denote s W.ρ_spec) ?_ η
          intro k η' ih
          refine ValDecl.checkGhostRank_correct _ { W with eta := η' } (henv.eta η') _ retTy s body
            argNames _ k _ self.name hswf hslen hlen_args (hag'.eta η') hpersist_owns himpl ?_
          intro vs gs argVars ghostVars st₁ ρ₁ Ψ hst_sub hρ_agree hargVars_mem hargVars_sort
            hargVars_lookup hghostVars_mem hghostVars_sort hghostVars_lookup hlen_vs hlen_gs
            hrank hev
          have hag₁ : W.agrees st₁.decls ρ₁ := hag'.step hst_sub hρ_agree
          have hlen_call : s.allArgs.length ≤ (vs ++ gs).length := by
            simp [Spec.allArgs]; omega
          have hlen_terms : s.allArgs.length =
              ((argVars ++ ghostVars).map fun c =>
                (Term.const (.uninterpreted c.name .value) : Term .value)).length := by
            have h₁ := hargVars_lookup.length_eq
            have h₂ := hghostVars_lookup.length_eq
            simp [Spec.allArgs]; omega
          have hterms_eval : Term.evalList ρ₁
              ((argVars ++ ghostVars).map fun c =>
                (Term.const (.uninterpreted c.name .value) : Term .value)) (vs ++ gs) := by
            rw [List.map_append]
            exact List.rel_append (constTerms_eval hargVars_lookup)
              (constTerms_eval hghostVars_lookup)
          simp only [ValDecl.ghostSelf, hself, hdec, GhostFunctions.Guard.declare] at hev
          cases hmwf : measure.term.checkWf (W.Δ_spec.declVars (Spec.argVars s.allArgs)) with
          | error msg => rw [hmwf] at hev; exact (VerifM.eval_fatal hev).elim
          | ok u =>
          cases u
          rw [hmwf] at hev
          have hmeasure_wf : measure.term.wfIn (W.Δ_spec.declVars (Spec.argVars s.allArgs)) :=
            Term.checkWf_ok hmwf
          have hev := VerifM.eval_decls (VerifM.eval_bind hev)
          set m := measure.term.subst (Spec.argSubst Subst.id s.allArgs
            ((argVars ++ ghostVars).map fun c =>
              (Term.const (.uninterpreted c.name .value) : Term .value))) with hm_def
          cases hmwf₂ : m.checkWf st₁.decls with
          | error msg => rw [hmwf₂] at hev; exact (VerifM.eval_fatal hev).elim
          | ok u =>
          cases u
          rw [hmwf₂] at hev
          have hm_wf : m.wfIn st₁.decls := Term.checkWf_ok hmwf₂
          have hstwf : st₁.decls.wf := (VerifM.eval.wf hev).namesDisjoint
          have hownsWf := (VerifM.eval.wf hev).ownsWf
          set rv := st₁.freshConst (some "rank") .int with hrv_def
          have hfresh : rv.name ∉ st₁.decls.allNames := st₁.freshConst_fresh (some "rank") .int
          have hev := VerifM.eval_define (VerifM.eval_bind hev) hm_wf
          set st₂ : State := { st₁ with decls := st₁.decls.addConst rv } with hst₂_def
          set ρ₂ := ρ₁.updateConst .int rv.name (Term.eval ρ₁ m) with hρ₂_def
          have hsub₂ : st₁.decls.Subset st₂.decls := Signature.Subset.subset_addConst _ _
          have hagree₂ : Env.agreeOn st₁.decls ρ₁ ρ₂ := Env.agreeOn_update_fresh_const hfresh
          have hr_wf : (Term.const (.uninterpreted rv.name .int) : Term .int).wfIn st₂.decls :=
            Term.const_wfIn_addConst_of_fresh (Δ := st₁.decls) (c := rv) hstwf hfresh
          have hrank_eq : (Term.eval ρ₂ (Term.const (.uninterpreted rv.name .int))).toNat =
              measure.denote s W.ρ_spec vs gs := by
            simp only [Term.eval_const_updateConst, hρ₂_def, Typed.Measure.denote]
            rw [Spec.eval_argSubst (Δ := W.Δ_spec) hlen_terms hterms_eval measure.term hmeasure_wf,
              Term.eval_agreeOn hmeasure_wf (Spec.argsEnv_agreeOn (Δ := W.Δ_spec)
                (Env.agreeOn_symm hag₁.agree) s.allArgs (vs ++ gs) hlen_call)]
          have hΨ := VerifM.eval_ret hev
          refine ⟨_, _, ρ₂, ?_, hagree₂, ?_, ?_, hΨ⟩
          · exact hsub₂
          · exact (SpatialContext.interp_agreeOn _ hownsWf hagree₂).1
          intro η'' f'' argTys'' retTy'' s'' guard'' hlookup''
          by_cases hg : f'' = g
          · subst hg
            simp only [List.lookup, beq_self_eq_true, Option.some.injEq,
              GhostFunctions.Entry.mk.injEq] at hlookup''
            obtain ⟨hty'', hguard''⟩ := hlookup''
            cases hty''; cases hguard''
            refine ⟨hr_wf, hmeasure_wf, ?_⟩
            rw [hrank_eq]
            exact ih _ hrank η''
          · have hne : (f'' == g) = false := by simpa using hg
            rw [List.lookup, hne] at hlookup''
            exact GhostFunctions.wellTyped.eta
              (hGf'.step (hst_sub.trans hsub₂) (Env.agreeOn_trans hρ_agree
                (Env.agreeOn_mono hst_sub hagree₂)) (Signature.wf_addConst hstwf hfresh))
              η'' f'' argTys'' retTy'' s'' guard'' hlookup''
    · have hne : (f' == f) = false := by simpa using hf
      rw [List.lookup, hne] at hlookup
      simp at hlookup

theorem ValDecl.checkGhost_correct (env : Verifier.Env) (W : TinyML.World) (henv : env.wf W)
    (Gf : GhostFunctions) (d : Typed.ValDecl)
    {st : State} {ρ : Env} (hag : W.agrees st.decls ρ)
    (hGf : GhostFunctions.wellTyped W st.decls ρ Gf)
    {Q : (TinyML.Var × GhostFunctions.Entry) → State → Env → Prop}
    (heval : SeqM.eval (ValDecl.checkGhost env Gf d) st ρ Q) :
    ∃ entry, GhostFunctions.wfIn W.Δ_spec W.Θ [entry] ∧ GhostFunctions.wellTyped W st.decls ρ [entry] ∧
      Q entry st ρ := by
  simp only [ValDecl.checkGhost] at heval
  split at heval
  · exact (SeqM.eval_fatal heval).elim
  · exact ValDecl.prove_correct env W henv Gf _ _ _ _ _ _ d.decreases hag hGf heval
  · exact (SeqM.eval_fatal heval).elim

theorem ValDecl.checkGhostFn_correct (env : Verifier.Env) (W : TinyML.World) (henv : env.wf W)
    (Gf : GhostFunctions) (d : Typed.ValDecl)
    {st : State} {ρ : Env} (hag : W.agrees st.decls ρ)
    (hGf : GhostFunctions.wellTyped W st.decls ρ Gf)
    {Q : GhostFunctions → State → Env → Prop}
    (heval : SeqM.eval (ValDecl.checkGhostFn env Gf d) st ρ Q) :
    ∃ fn, GhostFunctions.wfIn W.Δ_spec W.Θ fn ∧ GhostFunctions.wellTyped W st.decls ρ fn ∧ Q fn st ρ := by
  simp only [ValDecl.checkGhostFn] at heval
  cases hrel : d.relation with
  | none => simp only [hrel] at heval; exact ⟨[], nofun, GhostFunctions.wellTyped.empty W _ ρ,
      SeqM.eval_ret heval⟩
  | some rel =>
    obtain ⟨relName, ghost, _⟩ := rel
    cases ghost with
    | false =>
      simp only [hrel] at heval
      exact ⟨[], nofun, GhostFunctions.wellTyped.empty W _ ρ, SeqM.eval_ret heval⟩
    | true =>
      simp only [hrel] at heval
      cases hname : d.name.name with
      | none => simp only [hname] at heval; exact (SeqM.eval_fatal heval).elim
      | some f =>
        cases hbody : d.body with
        | fix self args retTy spec body =>
          match args, hbody with
          | [⟨some x, xty⟩], hbody =>
            simp only [hname, hbody] at heval
            obtain ⟨entry, hwf, hentry, hQ⟩ := ValDecl.prove_correct env W henv Gf f self
              [⟨some x, xty⟩] retTy body (Spec.ofRelation relName x) d.decreases hag hGf heval
            exact ⟨[entry], hwf, hentry, hQ⟩
          | [], hbody | ⟨none, _⟩ :: _, hbody | _ :: _ :: _, hbody =>
            simp only [hname, hbody] at heval; exact (SeqM.eval_fatal heval).elim
        | _ => simp only [hname, hbody] at heval; exact (SeqM.eval_fatal heval).elim

theorem ValDecl.publish_correct (env : Verifier.Env) (W : TinyML.World) (henv : env.wf W)
    (d : Typed.ValDecl) {st : State} {ρ : Env}
    {Q : GhostFunctions → State → Env → Prop}
    (heval : SeqM.eval (ValDecl.publish env d) st ρ Q) :
    ∃ unf, GhostFunctions.wfIn W.Δ_spec W.Θ unf ∧ GhostFunctions.wellTyped W st.decls ρ unf ∧
      Q unf st ρ := by
  simp only [ValDecl.publish] at heval
  cases hrel : d.relation with
  | none => simp only [hrel] at heval
            exact ⟨[], nofun, GhostFunctions.wellTyped.empty W _ ρ, SeqM.eval_ret heval⟩
  | some r =>
    simp only [hrel] at heval
    cases ht : r.transparency with
    | transparent => simp only [ht] at heval
                     exact ⟨[], nofun, GhostFunctions.wellTyped.empty W _ ρ, SeqM.eval_ret heval⟩
    | «opaque» =>
      simp only [ht] at heval
      split at heval
      · rename_i l ty _ _ hl _
        split at heval
        · rename_i entry hp
          obtain ⟨u, hok, heval⟩ := SeqM.eval_ofExcept (SeqM.eval_bind heval)
          cases u
          refine ⟨[entry], fun p hp' => ?_,
            Lemma.publish_wellTyped W st.decls ρ (Lemmas.ofDeclaration_sound henv.lemmas hl)
              (henv.signature ▸ hp),
            SeqM.eval_ret heval⟩
          cases List.mem_singleton.mp hp'
          refine ⟨Lemma.publish_guard hp, ?_⟩
          rw [henv.signature, henv.typeDeclarations]
          exact TinyML.Typ.checkWf_ok _ hok
        · exact (SeqM.eval_fatal heval).elim
      · exact (SeqM.eval_fatal heval).elim

theorem ValDecl.ghostEntries_correct (env : Verifier.Env) (W : TinyML.World) (henv : env.wf W)
    (Gf : GhostFunctions) (d : Typed.ValDecl)
    {st : State} {ρ : Env} (hag : W.agrees st.decls ρ)
    (hGf : GhostFunctions.wellTyped W st.decls ρ Gf)
    {Q : GhostFunctions → State → Env → Prop}
    (heval : SeqM.eval (ValDecl.ghostEntries env Gf d) st ρ Q) :
    ∃ fn, GhostFunctions.wfIn W.Δ_spec W.Θ fn ∧ GhostFunctions.wellTyped W st.decls ρ fn ∧ Q fn st ρ := by
  simp only [ValDecl.ghostEntries] at heval
  obtain ⟨fn, hfnwf, hfn, heval⟩ :=
    ValDecl.checkGhostFn_correct env W henv Gf d hag hGf (SeqM.eval_bind heval)
  obtain ⟨unf, hunfwf, hunf, heval⟩ :=
    ValDecl.publish_correct env W henv d (SeqM.eval_bind heval)
  exact ⟨fn ++ unf, GhostFunctions.wfIn_append hfnwf hunfwf, hfn.append hunf, SeqM.eval_ret heval⟩

end GhostDeclarations

namespace Verifier

open Typed (SpecEnv)

/-! ## Elaboration -/

/-- Encode one typechecked specification leaf into its value term and definedness
condition. The encoder environment is the identity over the spec-level names in
scope: `δ` carries real terms only *inside* a leaf — for let-expressions and
match payloads — so the names alone determine it. -/
private def translateLeaf (primitives : PrimEncodings) (Δ : Signature)
    (Γfn : FunCtx) (names : List String)
    (e : Typed.Expr) : Except String (Term .value × Formula) := do
  let c ← encode primitives Δ Γfn (names.map (fun n => (n, .var .value n))) e
    (Δ.allNames ++ names)
  let dv := Verifier.RelationalEncoding.Expr.toDefVal .id c
  .ok (dv.value, dv.defined)

/-- The environment elaboration resolves specifications against: the registry's
primitives, and leaf translation through bounded-quantifier lifting followed by
the relational FOL encoding. Lifting a leaf turns its quantifier occurrences
into calls of the lifted symbols, so the rewritten leaf resolves against the
spec functions extended by every lifting so far. `own` are the spec functions
the declaration itself defines, which its specification may call. -/
def Env.specEnv (env : Env) (own : FunCtx) : SpecEnv BoundedQuantifier.LiftState where
  primitive := env.registry.sigs
  -- `Typed.Decl.elaborate` sets the globals and the type variables.
  globals := TinyML.TyCtx.empty
  translate names e := fun st =>
    match BoundedQuantifier.rewriteLeaf e st with
    | .error msg => .error (.spec msg)
    | .ok (e', st') =>
      let Γ := env.specFunctions ++ own ++ st'.syms.map (fun s => (s.name, s.name))
      match translateLeaf env.registry.primitives (Intrinsic.sigOf env.registry) Γ names e' with
      | .error msg => .error (.spec msg)
      | .ok r => .ok (r, st')
  tvars := []

/-- The spec function a `[@@fn]` declaration defines. `Env.declareAndAssume`
re-derives it from the typed declaration and validates it, so nothing here is
trusted. -/
private def ownSpecFunctions : Untyped.Decl Untyped.SpecBody → FunCtx
  | .val_ d =>
    match d.name, d.relation with
    | .named f _, some rel => [(f, rel.name)]
    | _, _ => []
  | .type_ _ => []

/-- The payloads of the type `d` declares are well formed. -/
private def checkTypeDeclaration (Δ : Signature) (Θ : TinyML.TypeEnv) :
    Untyped.Decl Untyped.SpecBody → Except String Unit
  | .type_ dty =>
    match Θ dty.name with
    | some d => TinyML.Typ.checkWfList Δ Θ d.payloads
    | none => .ok ()
  | .val_ _ => .ok ()

/-- Elaborate `d` against `env`, and declare the spec functions it defines and
the bounded quantifiers its specifications lift. The spec functions come first,
because a lifted body may call them. -/
def Decl.declare (env : Env) (d : Untyped.Decl Untyped.SpecBody) :
    SeqM (Env × Option Typed.ValDecl) := do
  match Typed.Decl.elaborate (env.specEnv (ownSpecFunctions d)) env.typeDeclarations env.globals d
      { syms := env.liftings } with
  | .error err => SeqM.fatal (toString err)
  | .ok ((Θ, Γ, d'), lifted) => do
    SeqM.ofExcept (checkTypeDeclaration env.signature Θ d)
    let env' := { env with typeDeclarations := Θ, globals := Γ }
    let env' ← match d' with
      | some d' => env'.declareAndAssume d'
      | none => pure env'
    let env' ← env'.declareLiftings (lifted.syms.drop env.liftings.length)
    pure ({ env' with liftings := lifted.syms }, d')

/-! ## Checking -/

/-- Compile the body of `d` for safety. -/
def ValDecl.checkBody (env : Env) (S : Scope) (d : Typed.ValDecl) : VerifM Unit := do
  let _ ← compile env S d.body
  pure ()

/-- Check a typed declaration in the scope `S` of the values before it, and bind
what it defines. A specified function gets a constant, so the declarations after
it can use its name as a value. -/
def Decl.check (env : Env) (S : Scope) (d : Typed.ValDecl) : SeqM (Env × Scope) := do
  -- The entries are added after the handling below, because that handling
  -- drops the name from the ghost table when it binds a run-time value of it.
  let fn ← ValDecl.ghostEntries env S.ghostFns d
  match d.mode with
  | .ghost =>
    -- A ghost declaration binds no run-time value: it only becomes callable
    -- from the ghost code of the declarations that follow it.
    let entry ← ValDecl.checkGhost env S.ghostFns d
    pure (env, { S with ghostFns := fn ++ entry :: S.ghostFns,
                        runtimeBindings := S.runtimeBindings.remove entry.1 })
  | .runtime =>
    match d.name.name, d.body.spec? with
    | none, _ =>
      SeqM.check (ValDecl.checkBody env S d)
      pure (env, { S with ghostFns := fn ++ S.ghostFns })
    | some n, none => do
      -- A function definition runs no code. The new binding shadows any
      -- earlier one of the same name, which is therefore dropped: nothing here
      -- gives the new value a specification.
      if !d.body.isFunc then SeqM.check (ValDecl.checkBody env S d)
      pure (env, { S with ghostFns := fn ++ S.ghostFns.remove n,
                          runtimeBindings := S.runtimeBindings.remove n })
    | some n, some _ => do
      -- The value is a specified function: bind the name at the arrow it was
      -- verified at. The arrow's type variables are generalized, the
      -- verification having gone through at every assignment of them.
      SeqM.check (ValDecl.checkBody env S d)
      SeqM.ofExcept (TinyML.Typ.checkWf env.signature env.typeDeclarations d.body.ty)
      let fv : Decl.Const := ⟨Fresh.freshNumbers n env.signature.allNames, .value⟩
      SeqM.declConst fv
      pure ({ env with signature := env.signature.addConst fv },
            { S with ghostFns := fn ++ S.ghostFns.remove n,
                     runtimeBindings := (n, fv) :: S.runtimeBindings,
                     typingContext := S.typingContext.extendScheme n
                       (TinyML.Scheme.gen d.body.ty) })

/-- Elaborate and declare `d`, then check it. -/
def Decl.declareAndCheck (env : Env) (S : Scope) (d : Untyped.Decl Untyped.SpecBody) :
    SeqM (Env × Scope) := do
  let (env', d') ← Decl.declare env d
  match d' with
  | some d' => Decl.check env' S d'
  | none => pure (env', S)

end Verifier

namespace Verifier

variable {env env' : Env} {S : Scope} {st st' : State} {ρ ρ' : _root_.Env}
  {γ : Runtime.Subst}

/-! ## Declaring -/

omit [MicaGS HasLC.hasLC Sig] in
private theorem checkTypeDeclaration_ok {Δ : Signature} {Θ : TinyML.TypeEnv}
    {dty : Untyped.TypeDecl} (h : checkTypeDeclaration Δ Θ (.type_ dty) = .ok ()) :
    ∀ dd, Θ dty.name = some dd → ∀ p ∈ dd.payloads, TinyML.Typ.wfIn Δ Θ p := by
  intro dd hT
  simp only [checkTypeDeclaration, hT] at h
  exact TinyML.Typ.checkWfList_ok _ h

theorem Decl.declare_correct {d : Untyped.Decl Untyped.SpecBody}
    {Q : Env × Option Typed.ValDecl → State → _root_.Env → Prop}
    (henv : env.supportedBy st ρ) (hS : S.supportedBy env st ρ γ)
    (howns : st.owns = []) (hvars : st.decls.vars = [])
    (heval : SeqM.eval (Decl.declare env d) st ρ Q) :
    ∃ env' d' st' ρ', env'.supportedBy st' ρ' ∧ S.supportedBy env' st' ρ' γ ∧
      st'.owns = [] ∧ st'.decls.vars = [] ∧ env'.registry = env.registry ∧ (env.world ρ).Subset (env'.world ρ') ∧
      d'.bind Typed.ValDecl.runtime? = d.runtime ∧ Q (env', d') st' ρ' := by
  have hst := SeqM.eval_wf heval
  cases helab : Typed.Decl.elaborate (env.specEnv (ownSpecFunctions d)) env.typeDeclarations
      env.globals d { syms := env.liftings } with
  | error err =>
    simp only [Decl.declare, helab] at heval
    exact (SeqM.eval_fatal heval).elim
  | ok r =>
    obtain ⟨⟨Θ, Γ, d'⟩, lifted⟩ := r
    simp only [Decl.declare, helab] at heval
    obtain ⟨hΘext, hΘsame⟩ := Typed.Decl.elaborate_types helab
    have hrt := Typed.Decl.elaborate_runtime _ _ _ d helab
    -- The type declaration's own payloads are checked; the others were before.
    obtain ⟨u, hcheck, h2⟩ := SeqM.eval_ofExcept (SeqM.eval_bind heval)
    cases u
    have htypes : TinyML.TypeEnv.wfIn st.decls Θ := by
      intro T dd hT p hp
      by_cases hnew : ∃ dty, d = .type_ dty ∧ T = dty.name
      · obtain ⟨dty, rfl, rfl⟩ := hnew
        have := checkTypeDeclaration_ok hcheck dd hT p hp
        rwa [henv.signature] at this
      · have hold : Θ T = env.typeDeclarations T :=
          hΘsame T fun dty hd hT' => hnew ⟨dty, hd, hT'⟩
        rw [hold] at hT
        exact TinyML.Typ.wfIn_mono (Signature.Subset.refl _) hst.namesDisjoint hΘext
          (henv.types T dd hT p hp)
    have hlaw := Registry.primitives_lawful henv.sound
    have hinv0 : Env.SpecInv env.registry Θ { env with typeDeclarations := Θ, globals := Γ } st ρ :=
      ⟨rfl, rfl, henv.signature, howns, hvars, hst.namesDisjoint, henv.specFunctionsWf,
        henv.specFunctionsAgree, henv.lemmas⟩
    obtain ⟨env1, st1, ρ1, hinv1, hsub1, hag1, h4⟩ : ∃ env1 st1 ρ1,
        Env.SpecInv env.registry Θ env1 st1 ρ1 ∧ st.decls.Subset st1.decls ∧
        Env.agreeOn st.decls ρ ρ1 ∧
        SeqM.eval (do
          let env' ← env1.declareLiftings (lifted.syms.drop env.liftings.length)
          pure ({ env' with liftings := lifted.syms }, d')) st1 ρ1 Q := by
      cases d' with
      | none => exact ⟨_, st, ρ, hinv0, Signature.Subset.refl _, Env.agreeOn_refl, h2⟩
      | some dd => exact Env.declareAndAssume_correct hlaw dd _ st ρ hinv0 (SeqM.eval_bind h2)
    obtain ⟨env2, st2, ρ2, hinv2, hsub2, hag2, h5⟩ :=
      Env.declareLiftings_correct hlaw _ env1 st1 ρ1 hinv1 (SeqM.eval_bind h4)
    have hsub := hsub1.trans hsub2
    have hag := Env.agreeOn_trans hag1 (Env.agreeOn_mono hsub1 hag2)
    have hreg : env2.registry = env.registry := hinv2.registry
    have hΘ2 : env2.typeDeclarations = Θ := hinv2.types
    have hW : (env.world ρ).Subset ({ env2 with liftings := lifted.syms }.world ρ2) :=
      ⟨by simp [Env.world, hreg], rfl, fun T dd hT => by simpa [Env.world, hΘ2] using hΘext T dd hT,
        by simpa [Env.world, henv.signature, hinv2.signature] using hsub,
        by simpa [Env.world, henv.signature] using hag⟩
    refine ⟨{ env2 with liftings := lifted.syms }, d', st2, ρ2, ?_, ?_, hinv2.owns, hinv2.vars,
      hreg, hW, hrt,
      SeqM.eval_ret h5⟩
    · exact
        { sound := hreg ▸ henv.sound
          signature := hinv2.signature
          specFunctionsWf := hinv2.Γwf
          specFunctionsAgree := hinv2.Γagree
          lemmas := hinv2.lemmas
          symbols := hreg ▸ Registry.symSubset_mono henv.symbols hsub
          interpretations := hreg ▸ Registry.symAgree_agreeOn henv.interpretations henv.symbols hag
          types := by
            rw [show ({ env2 with liftings := lifted.syms } : Env).typeDeclarations = Θ from hΘ2]
            intro T dd hT p hp
            exact TinyML.Typ.wfIn_mono hsub hinv2.wf (fun _ _ h => h) (htypes T dd hT p hp) }
    · exact Scope.supportedBy_mono hS henv hinv2.wf hsub hag
        (fun T dd hT => by simpa [hΘ2] using hΘext T dd hT) hW

/-! ## Checking -/

/-- The body runs safely, and a frame `Φ` survives it. -/
theorem ValDecl.checkBody_correct (env : Env) (W : TinyML.World) (henv : env.wf W)
    (Gf : GhostFunctions) (B : Bindings) (Γ : TinyML.TyCtx) (d : Typed.ValDecl) (γ : Runtime.Subst)
    (st : State) (ρ : _root_.Env)
    (hS : (⟨Gf, Bindings.empty, B, Γ⟩ : Scope).wfIn W st.decls ρ Runtime.Subst.id γ)
    {Q : Unit → State → _root_.Env → Prop}
    (heval : VerifM.eval (ValDecl.checkBody env ⟨Gf, Bindings.empty, B, Γ⟩ d) st ρ Q) (Φ : iProp) :
    □ st.sl W ρ ∗ Bindings.typedSubst W B Γ γ ∗ Φ ⊢
      wp W.pctx (d.body.runtime.subst γ) (fun _ => Φ) := by
  simp only [ValDecl.checkBody] at heval
  have hcomp := compile_correct d.body env W _ _ _ (R := iprop(□ st.sl W ρ ∗ Φ))
    (Φ := fun _ => Φ) henv hS (VerifM.eval_bind heval)
    (fun _ _ _ _ _ _ _ => by
      istart
      iintro ⟨_, _, Hctx⟩
      icases Hctx with ⟨_, HΦ⟩
      iexact HΦ)
  refine (BIBase.Entails.trans ?_ hcomp)
  istart
  iintro ⟨#Hsl, #HT, HΦ⟩
  isplitl []
  · iexact Hsl
  · isplitl []
    · iapply Scope.typed_runtimeBindings
      iexact HT
    · isplitl []
      · iexact Hsl
      · iexact HΦ

/-- A specified function's value is typed at the arrow it was verified at.
    Stated without a `wp` for the same reason as `compileFix_typed`: the caller
    needs it once per assignment. -/
theorem ValDecl.checkBody_typed (env : Env) (W : TinyML.World) (henv : env.wf W)
    (Gf : GhostFunctions) (B : Bindings) (Γ : TinyML.TyCtx) (d : Typed.ValDecl) (γ : Runtime.Subst)
    (self : Typed.Binder) (args : List Typed.Binder) (retTy : TinyML.Typ)
    (s : Spec TinyML.Typ) (body : Typed.Expr)
    (hbody : d.body = .fix self args retTy (some s) body)
    (st : State) (ρ : _root_.Env)
    (hS : (⟨Gf, Bindings.empty, B, Γ⟩ : Scope).wfIn W st.decls ρ Runtime.Subst.id γ)
    {Q : Unit → State → _root_.Env → Prop}
    (heval : VerifM.eval (ValDecl.checkBody env ⟨Gf, Bindings.empty, B, Γ⟩ d) st ρ Q) :
    Bindings.typedSubst W B Γ γ ⊢
      TinyML.ValHasType W
        (Runtime.Val.fix self.runtime (args.map (·.runtime))
          (body.runtime.subst ((γ.remove' self.runtime).removeAll' (args.map (·.runtime)))))
        d.body.ty := by
  simp only [ValDecl.checkBody] at heval
  have hty : d.body.ty = .arrow (args.map Typed.Binder.WithTypeVars.ty) retTy (some s) := by
    rw [hbody]; simp [Typed.Expr.WithTypeVars.ty]
  rw [hty]
  have hc := VerifM.eval_bind heval
  rw [hbody] at hc
  exact Scope.typed_runtimeBindings.trans
    (compileFix_typed env W henv _ Runtime.Subst.id γ self args retTy s body
      (compile_correct body) hS hc)

theorem Decl.check_correct {d : Typed.ValDecl} {Q : Env × Scope → State → _root_.Env → Prop}
    (henv : env.supportedBy st ρ) (hS : S.supportedBy env st ρ γ) (hG : S.ghostBindings = [])
    (howns : st.owns = []) (hvars : st.decls.vars = [])
    (heval : SeqM.eval (Decl.check env S d) st ρ Q) (P : Runtime.Program)
    (hk : ∀ env' S' st' ρ' γ', env'.supportedBy st' ρ' → S'.supportedBy env' st' ρ' γ' →
      S'.ghostBindings = [] → st'.owns = [] → st'.decls.vars = [] →
      env'.registry = env.registry → Q (env', S') st' ρ' →
      S'.runtimeBindings.schemeSubst (env'.world ρ') S'.typingContext γ' ⊢
        pwp env.registry.primCtx (P.subst γ')) :
    S.runtimeBindings.schemeSubst (env.world ρ) S.typingContext γ ⊢
      pwp env.registry.primCtx (Runtime.Program.subst (d.runtime?.toList ++ P) γ) := by
  obtain ⟨Gf, G, B, Γ⟩ := S
  obtain rfl : G = [] := hG
  have hst := SeqM.eval_wf heval
  have hW := Env.wf_of_supportedBy henv hst hvars
  have hag := Env.agrees_of_supportedBy henv
  have hSwf := Scope.wfIn_of_supportedBy henv hS rfl Runtime.Subst.id
  have hsig : env.signature = st.decls := henv.signature
  simp only [Decl.check] at heval
  obtain ⟨fn, hfnwf, hfn, heval⟩ :=
    ValDecl.ghostEntries_correct env _ hW Gf d hag hS.ghostFns (SeqM.eval_bind heval)
  replace hfnwf : fn.wfIn st.decls env.typeDeclarations :=
    hsig ▸ (hfnwf : fn.wfIn env.signature env.typeDeclarations)
  have hsl : ⊢ □ st.sl (env.world ρ) ρ := State.sl_of_owns_nil howns
  cases hmode : d.mode with
  | ghost =>
    simp only [hmode] at heval
    obtain ⟨entry, hentrywf, hentry, heval⟩ :=
      ValDecl.checkGhost_correct env _ hW Gf d hag hS.ghostFns (SeqM.eval_bind heval)
    replace hentrywf : GhostFunctions.wfIn st.decls env.typeDeclarations [entry] :=
      hsig ▸ (hentrywf : GhostFunctions.wfIn env.signature env.typeDeclarations [entry])
    have hk' := hk env ⟨fn ++ entry :: Gf, [], B.remove entry.1, Γ⟩ st ρ γ henv
      { closed := hS.closed
        types := hS.types
        ghostFnsWf := GhostFunctions.wfIn_append hfnwf (GhostFunctions.wfIn_append hentrywf hS.ghostFnsWf)
        ghostFns := hfn.append (hentry.append hS.ghostFns)
        runtimeLinked := Bindings.agreeOnLinked_remove hS.runtimeLinked entry.1
        runtimeDeclared := Bindings.wfIn_remove hS.runtimeDeclared entry.1 }
      rfl howns hvars rfl (SeqM.eval_ret heval)
    simpa [Typed.ValDecl.runtime?, hmode] using Bindings.schemeSubst_remove.trans hk'
  | runtime =>
    have hunfold :
        wp (env.world ρ).pctx (d.body.runtime.subst γ) (fun v =>
          pwp env.registry.primCtx
            (P.subst (Runtime.Subst.updateBinder d.name.runtime v γ)))
        ⊢ pwp env.registry.primCtx (Runtime.Program.subst (d.runtime?.toList ++ P) γ) := by
      simp only [Typed.ValDecl.runtime?, hmode, Typed.ValDecl.runtime, Option.toList_some,
        List.singleton_append, Runtime.Program.subst, Runtime.Decl.subst]
      refine BIBase.Entails.trans (wp.mono fun v => ?_) pwp_cons
      rw [Runtime.Program.subst_remove_update]
      exact .rfl
    refine BIBase.Entails.trans ?_ hunfold
    simp only [hmode] at heval
    cases hname : d.name.name with
    | none =>
      simp only [hname] at heval
      have hupd : ∀ v, Runtime.Subst.updateBinder d.name.runtime v γ = γ := by
        intro v; simp [Typed.Binder.runtime_of_name_none hname, Runtime.Subst.updateBinder]
      obtain ⟨hchk, heval⟩ := SeqM.eval_check (SeqM.eval_bind heval)
      have hk' := hk env ⟨fn ++ Gf, [], B, Γ⟩ st ρ γ henv
        { closed := hS.closed
          types := hS.types
          ghostFnsWf := GhostFunctions.wfIn_append hfnwf hS.ghostFnsWf
          ghostFns := hfn.append hS.ghostFns
          runtimeLinked := hS.runtimeLinked
          runtimeDeclared := hS.runtimeDeclared }
        rfl howns hvars rfl (SeqM.eval_ret heval)
      have hwp := ValDecl.checkBody_correct env _ hW Gf B Γ d γ st ρ hSwf hchk
        (pwp env.registry.primCtx (P.subst γ))
      simp only [hupd]
      refine BIBase.Entails.trans ?_ hwp
      istart
      iintro #H
      isplitl []
      · iapply hsl
      · isplitl []
        · iapply Bindings.typedSubst_of_schemeSubst
          iexact H
        · iapply hk'
          iexact H
    | some n =>
      have hname_rt : d.name.runtime = .named n := Typed.Binder.runtime_of_name_some hname
      have hupd : ∀ v, Runtime.Subst.updateBinder d.name.runtime v γ = γ.update n v := by
        intro v; simp [hname_rt, Runtime.Subst.updateBinder]
      simp only [hupd]
      cases hspec : d.body.spec? with
      | none =>
        simp only [hname, hspec] at heval
        have hS' : ∀ v, Scope.supportedBy ⟨fn ++ Gf.remove n, [], B.remove n, Γ⟩
            env st ρ (γ.update n v) := fun v =>
          { closed := hS.closed
            types := hS.types
            ghostFnsWf := GhostFunctions.wfIn_append hfnwf (GhostFunctions.wfIn_remove hS.ghostFnsWf n)
            ghostFns := hfn.append (hS.ghostFns.remove n)
            runtimeLinked := Bindings.agreeOnLinked_remove_update hS.runtimeLinked n v
            runtimeDeclared := Bindings.wfIn_remove hS.runtimeDeclared n }
        by_cases hf : d.body.isFunc
        · rw [if_neg (by simp [hf])] at heval
          have hQ := SeqM.eval_ret (SeqM.eval_ret (SeqM.eval_bind heval))
          obtain ⟨self, args, retTy, spec, body, hbody⟩ := Typed.Expr.isFunc_elim hf
          have hbody_rt : d.body.runtime.subst γ =
              Runtime.Expr.fix self.runtime (args.map (·.runtime))
                (body.runtime.subst ((γ.remove' self.runtime).removeAll'
                  (args.map (·.runtime)))) := by
            rw [hbody]; conv_lhs => unfold Typed.Expr.WithTypeVars.runtime
            simp only [Runtime.Expr.subst_fix]
          rw [hbody_rt]
          apply PrimitiveLaws.wp_func
          exact Bindings.schemeSubst_remove_update.trans
            (hk env ⟨fn ++ Gf.remove n, [], B.remove n, Γ⟩ st ρ _ henv (hS' _) rfl howns hvars rfl hQ)
        · rw [if_pos (by simpa using hf)] at heval
          obtain ⟨hchk, heval⟩ := SeqM.eval_check (SeqM.eval_bind heval)
          have hwp := ValDecl.checkBody_correct env _ hW Gf B Γ d γ st ρ hSwf hchk iprop(emp)
          refine PrimitiveLaws.wp_strengthen_persistent (P := fun _ => iprop(emp)) (hwp := ?_)
            (hpost := fun v => ?_)
          · istart
            iintro #H
            iapply hwp
            isplitl []
            · iapply hsl
            · isplitl []
              · iapply Bindings.typedSubst_of_schemeSubst
                iexact H
              · iempintro
          · exact wand_intro (sep_elim_left.trans (Bindings.schemeSubst_remove_update.trans
              (hk env ⟨fn ++ Gf.remove n, [], B.remove n, Γ⟩ st ρ (γ.update n v) henv (hS' v)
                rfl howns hvars rfl (SeqM.eval_ret heval))))
      | some sp =>
        simp only [hname, hspec] at heval
        obtain ⟨self, args, retTy, body, hbody⟩ := Typed.Expr.spec?_elim hspec
        obtain ⟨hchk, heval⟩ := SeqM.eval_check (SeqM.eval_bind heval)
        obtain ⟨u, hwfty, heval⟩ := SeqM.eval_ofExcept (SeqM.eval_bind heval)
        obtain ⟨hfresh, heval⟩ := SeqM.eval_declConst (SeqM.eval_bind heval)
        set fv : Decl.Const := ⟨Fresh.freshNumbers n env.signature.allNames, .value⟩
        set v := Runtime.Val.fix self.runtime (args.map (·.runtime))
          (body.runtime.subst ((γ.remove' self.runtime).removeAll' (args.map (·.runtime))))
        set ρ₁ := ρ.updateConst .value fv.name v
        set st₁ : State := { st with decls := st.decls.addConst fv }
        set env₁ : Env := { env with signature := env.signature.addConst fv }
        have hwf₁ : st₁.decls.wf := Signature.wf_addConst hst.namesDisjoint hfresh
        have hsub₁ : st.decls.Subset st₁.decls := Signature.Subset.subset_addConst _ _
        have hag₁ : Env.agreeOn st.decls ρ ρ₁ := Env.agreeOn_update_fresh_const hfresh
        have hty : TinyML.Typ.wfIn st.decls env.typeDeclarations d.body.ty :=
          hsig ▸ TinyML.Typ.checkWf_ok _ hwfty
        have hW₁ : (env.world ρ).Subset (env₁.world ρ₁) :=
          ⟨rfl, rfl, fun _ _ h => h, by simpa [Env.world, env₁, hsig] using hsub₁,
            by simpa [Env.world, hsig] using hag₁⟩
        have henv₁ : env₁.supportedBy st₁ ρ₁ :=
          { sound := henv.sound
            signature := by simp [env₁, st₁, hsig]
            specFunctionsWf := FunCtx.wfIn_mono henv.specFunctionsWf hsub₁
            specFunctionsAgree := henv.specFunctionsAgree.updateConst _ _ _
            lemmas := henv.lemmas.mono hsub₁ hag₁ hwf₁
            symbols := Registry.symSubset_mono henv.symbols hsub₁
            interpretations := Registry.symAgree_agreeOn henv.interpretations henv.symbols hag₁
            types := fun T dd hT p hp =>
              TinyML.Typ.wfIn_mono hsub₁ hwf₁ (fun _ _ h => h) (henv.types T dd hT p hp) }
        have hfnwf' := GhostFunctions.wfIn_append hfnwf (GhostFunctions.wfIn_remove hS.ghostFnsWf n)
        have hS₁ : Scope.supportedBy ⟨fn ++ Gf.remove n, [], (n, fv) :: B,
            Γ.extendScheme n (TinyML.Scheme.gen d.body.ty)⟩ env₁ st₁ ρ₁ (γ.update n v) :=
          { closed := hS.closed.extendScheme n (TinyML.Scheme.gen_free _)
            types := fun x s hx => by
              by_cases hxn : x = n
              · subst hxn
                simp [TinyML.TyCtx.extendScheme] at hx
                subst hx
                exact TinyML.Typ.wfIn_mono hsub₁ hwf₁ (fun _ _ h => h) hty
              · have hx' : Γ x = some s := by
                  simpa [TinyML.TyCtx.extendScheme, hxn] using hx
                exact TinyML.Typ.wfIn_mono hsub₁ hwf₁ (fun _ _ h => h) (hS.types x s hx')
            ghostFnsWf := GhostFunctions.wfIn_mono hfnwf' hsub₁ hwf₁ fun _ _ h => h
            ghostFns := GhostFunctions.wellTyped_of_subset hW₁ (Env.typesWf_of_supportedBy henv)
              (by simpa [Env.world, hsig] using hfnwf') (hfn.append (hS.ghostFns.remove n))
            runtimeLinked := Bindings.agreeOnLinked_cons_update
              (Bindings.agreeOnLinked_agreeOn hS.runtimeLinked hag₁ hS.runtimeDeclared) rfl
              (by simp [ρ₁, Env.updateConst])
            runtimeDeclared := Bindings.wfIn_cons hS.runtimeDeclared }
        have hk' := hk env₁ _ st₁ ρ₁ _ henv₁ hS₁ rfl howns hvars rfl (SeqM.eval_ret (heval v))
        -- The value has its scheme: the check went through at every assignment.
        have hval : Bindings.schemeSubst (env.world ρ) B Γ γ ⊢
            TinyML.ValHasScheme (env₁.world ρ₁) v (TinyML.Scheme.gen d.body.ty) := by
          unfold TinyML.ValHasScheme
          refine forall_intro fun η => ?_
          set η' := TinyML.SemTypeAssign.override (env.world ρ).eta
            (TinyML.Scheme.gen d.body.ty).tparams η
          have htyped := ValDecl.checkBody_typed env _ (hW.eta η') Gf B Γ d γ self args retTy sp
            body hbody st ρ (hSwf.eta η') hchk
          refine (Bindings.schemeSubst_eta hS.closed η').trans
            (Bindings.typedSubst_of_schemeSubst.trans (htyped.trans ?_))
          exact (TinyML.ValueRelation.agreeOn_iff (TinyML.ValHasType.agreeOn
            (TinyML.World.subset_refl _) (TinyML.World.subset_withEta hW₁ η')
            (Env.typesWf_of_supportedBy henv)) (by simpa [Env.world, hsig] using hty) v).1
        rw [Typed.Expr.runtime_subst_of_fix hbody]
        refine PrimitiveLaws.wp_func ?_
        refine BIBase.Entails.trans ?_ hk'
        istart
        iintro #H
        iapply Bindings.schemeSubst_cons
        · iapply (Bindings.schemeSubst_of_subset hW₁ (Env.typesWf_of_supportedBy henv)
            (fun x s hx => by simpa [Env.world, hsig] using hS.types x s hx))
          iexact H
        · iapply hval
          iexact H

theorem Decl.declareAndCheck_correct {d : Untyped.Decl Untyped.SpecBody}
    {Q : Env × Scope → State → _root_.Env → Prop}
    (henv : env.supportedBy st ρ) (hS : S.supportedBy env st ρ γ) (hG : S.ghostBindings = [])
    (howns : st.owns = []) (hvars : st.decls.vars = [])
    (heval : SeqM.eval (Decl.declareAndCheck env S d) st ρ Q) (P : Runtime.Program)
    (hk : ∀ env' S' st' ρ' γ', env'.supportedBy st' ρ' → S'.supportedBy env' st' ρ' γ' →
      S'.ghostBindings = [] → st'.owns = [] → st'.decls.vars = [] →
      env'.registry = env.registry → Q (env', S') st' ρ' →
      S'.runtimeBindings.schemeSubst (env'.world ρ') S'.typingContext γ' ⊢
        pwp env.registry.primCtx (P.subst γ')) :
    S.runtimeBindings.schemeSubst (env.world ρ) S.typingContext γ ⊢
      pwp env.registry.primCtx (Runtime.Program.subst (d.runtime.toList ++ P) γ) := by
  simp only [Decl.declareAndCheck] at heval
  obtain ⟨env', d', st', ρ', henv', hS', howns', hvars', hreg, hW, hrt, heval⟩ :=
    Decl.declare_correct henv hS howns hvars (SeqM.eval_bind heval)
  refine (Bindings.schemeSubst_of_subset hW (Env.typesWf_of_supportedBy henv)
    (fun x s hx => by simpa [Env.world, henv.signature] using hS.types x s hx)).trans ?_
  rw [← hrt]
  cases d' with
  | none =>
    simpa using hk env' S st' ρ' γ henv' hS' hG howns' hvars' hreg (SeqM.eval_ret heval)
  | some dd =>
    have h := Decl.check_correct henv' hS' hG howns' hvars' heval P
      (fun env'' S'' st'' ρ'' γ'' h1 h2 hG'' ho hv h3 h4 =>
        hreg ▸ hk env'' S'' st'' ρ'' γ'' h1 h2 hG'' ho hv (h3.trans hreg) h4)
    rw [hreg] at h
    simpa using h

end Verifier

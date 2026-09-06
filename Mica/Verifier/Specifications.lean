-- SUMMARY: Verifier operations on function specifications: the call and implementation protocols and their correctness.
import Mica.SourceTinyML.Typed
import Mica.FOL.Printing
import Mica.Verifier.PrimitiveLaws
import Mica.Verifier.Monad
import Mica.Verifier.Assertions
import Mica.Verifier.Utils
import Mica.Verifier.PredicateTransformers
import Mica.Base.Fresh
import Mathlib.Data.Finmap

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]

/-!
# Specifications

The call and implementation operations for `Spec`, built on top of `PredTrans`,
with their correctness proofs. `Spec.isPrecondFor`, the semantics, lives in
`Mica/SourceTinyML/Semantics.lean`.
-/

-- ---------------------------------------------------------------------------
-- Spec
-- ---------------------------------------------------------------------------

namespace Spec

/-! ## Definitions -/

/-- The list of SMT variables corresponding to a spec's arguments. -/
def argVars (args : List String) : List Var :=
  args.map fun name => ⟨name, .value⟩

/-- A spec is well-formed when its predicate transformer is well-formed in the
    context extended with all argument variables. -/
def wfIn (spec : Spec TinyML.Typ) (Δ : Signature) : Prop :=
  PredTrans.wfIn (Δ.declVars (argVars spec.allArgs)) spec.pred

def checkWf (spec : Spec TinyML.Typ) (Δ : Signature) : Except String Unit :=
  PredTrans.checkWf (Δ.declVars (argVars spec.allArgs)) spec.pred

/-- Declare argument variables, check types, and assume equalities for a spec call.
    The argument names come from the spec and the argument types from the enclosing
    arrow. Returns the updated substitution. -/
def declareArgs (σ : FiniteSubst) :
    List String → List TinyML.Typ → List (TinyML.Typ × Term .value) → VerifM FiniteSubst
  | [], [], [] => pure σ
  | name :: names, ty :: tys, (targ, sarg) :: sargs => do
    if targ = ty then pure ()
    else VerifM.fatal s!"type mismatch in call to spec"
    let argVar ← VerifM.decl (some name) .value
    let σ' := σ.rename ⟨name, .value⟩ argVar.name
    VerifM.assume (.pure (.eq .value (.const (.uninterpreted argVar.name .value)) sarg))
    declareArgs σ' names tys sargs
  | _, _, _ => VerifM.fatal "wrong number of arguments"

/-- Full call protocol for a spec: declare argument variables, assume they equal the
    compiled argument terms, check argument types, then invoke `PredTrans.call`. The
    argument and result types come from the enclosing arrow. -/
def call (σ : FiniteSubst)
    (argTys : List TinyML.Typ) (retTy : TinyML.Typ)
    (s : Spec TinyML.Typ) (sargs sgargs : List (TinyML.Typ × Term .value)) :
    VerifM (TinyML.Typ × Term .value) := do
  let σ' ← declareArgs σ s.args argTys sargs
  let σ'' ← declareArgs σ' (s.ghost.map Prod.fst) (s.ghost.map Prod.snd) sgargs
  let result ← PredTrans.call σ'' s.pred
  VerifM.assumeAll (TinyML.typeConstraints retTy result)
  pure (retTy, result)

/-- Declare implementation argument variables: for each name/type pair,
    declare a fresh variable, assume its type constraints, and rename in `σ`.
    Returns the final substitution and the list of declared argument variables. -/
def declareImplArgs (σ : FiniteSubst) :
    List String → List TinyML.Typ → VerifM (FiniteSubst × List FOL.Const)
  | [], [] => pure (σ, [])
  | name :: names, ty :: tys => do
    let argVar ← VerifM.decl (some name) .value
    VerifM.assumeAll (TinyML.typeConstraints ty (.const (.uninterpreted argVar.name .value)))
    let σ' := σ.rename ⟨name, .value⟩ argVar.name
    let (σ'', vars) ← declareImplArgs σ' names tys
    pure (σ'', argVar :: vars)
  | _, _ => VerifM.fatal "wrong number of arguments"

/-- Full implementation protocol for a spec: declare argument variables,
    assume type constraints, then invoke `PredTrans.implement`. Dual to `call`.
    The argument types come from the enclosing arrow. -/
def implement (Δ_base : Signature) (argTys : List TinyML.Typ) (s : Spec TinyML.Typ)
    (body : List FOL.Const → List FOL.Const → VerifM (Term .value)) : VerifM Unit := do
  let (σ, argVars) ← declareImplArgs (FiniteSubst.base Δ_base) s.args argTys
  let (σ', ghostVars) ← declareImplArgs σ (s.ghost.map Prod.fst) (s.ghost.map Prod.snd)
  PredTrans.implement σ' s.pred (body argVars ghostVars)

/-! ## Precondition Proofs -/
section Precondition

/-- Fold `wp_fix'`'s tupled recursive obligation into a spec precondition;
    the two differ only by currying the typing hypothesis and the predicate transformer. -/
theorem isPrecondFor_intro (W : TinyML.World) (V : TinyML.ValueRelation)
    (argTys : List TinyML.Typ) (retTy : TinyML.Typ) (s : Spec TinyML.Typ)
    (f : Runtime.Val) :
    iprop(□ ∀ (ρ : Env) (vs gs : List Runtime.Val) (P : Runtime.Val → iProp),
      (⌜Env.agreeOn W.Δ_spec W.ρ_spec ρ⌝ ∗ ⌜vs.length = argTys.length⌝ ∗
        ⌜gs.length = s.ghost.length⌝ ∗
        ▷ TinyML.ValsRel V vs argTys ∗
        ▷ TinyML.ValsRel V gs (s.ghost.map Prod.snd) ∗
        ▷ PredTrans.apply V (fun r => V r retTy -∗ P r) s.pred
          (argsEnv ρ s.allArgs (vs ++ gs))) -∗
        wp W.pctx (Runtime.Expr.app (.val f) (vs.map Runtime.Expr.val)) P) ⊢
      s.isPrecondFor W V argTys retTy f := by
  unfold isPrecondFor
  iintro #H
  imodintro
  iintro %ρ %Φ %vs %gs Hagree Hlen Hglen Htyped Hgtyped Hpred
  ispecialize H $$ %ρ %vs %gs %Φ
  iapply H
  iframe

/-- Löb-style rule for spec preconditions on `fix`: to prove
    `s.isPrecondFor W (.fix f args e)`, assume it as the recursive hypothesis and
    prove the `wp` of the body (after the usual fix-substitution). -/
theorem isPrecondFor_fix {W : TinyML.World} {V : TinyML.ValueRelation}
    {argTys : List TinyML.Typ} {retTy : TinyML.Typ} {s : Spec TinyML.Typ}
    {f : Runtime.Binder} {args : List Runtime.Binder} {e : Runtime.Expr}
    {R : iProp}
    (hargs : args.length = s.args.length)
    (hargTys : argTys.length = s.args.length)
    (h : R ⊢ □ (s.isPrecondFor W V argTys retTy (.fix f args e) -∗
        ∀ (ρ : Env) (vs gs : List Runtime.Val) (P : Runtime.Val → iProp),
          ⌜Env.agreeOn W.Δ_spec W.ρ_spec ρ⌝ -∗
          ⌜gs.length = s.ghost.length⌝ -∗
          TinyML.ValsRel V vs argTys -∗
          TinyML.ValsRel V gs (s.ghost.map Prod.snd) -∗
          PredTrans.apply V (fun r => V r retTy -∗ P r) s.pred
              (argsEnv ρ s.allArgs (vs ++ gs)) -∗
          wp W.pctx (e.subst ((Runtime.Subst.id.updateBinder f (.fix f args e)).updateAllBinder args vs)) P)) :
    R ⊢ s.isPrecondFor W V argTys retTy (.fix f args e) := by
  refine (SpatialContext.wp_fix' (pctx := W.pctx) (f := f) (args := args) (e := e) (Φ := fun P vs =>
      iprop(∃ (ρ : Env) (gs : List Runtime.Val),
        ⌜Env.agreeOn W.Δ_spec W.ρ_spec ρ⌝ ∗ ⌜gs.length = s.ghost.length⌝ ∗
          TinyML.ValsRel V vs argTys ∗
          TinyML.ValsRel V gs (s.ghost.map Prod.snd) ∗
          PredTrans.apply V (fun r => V r retTy -∗ P r) s.pred
            (argsEnv ρ s.allArgs (vs ++ gs)))) (h.trans ?_)).trans ?_
  · istart
    iintro #HR
    imodintro
    iintro #IH %vs %P %hlen Hpre
    ispecialize HR $$ [IH]
    · unfold isPrecondFor
      imodintro
      iintro %ρ %Φ %vs' %gs' %hagr' %hlen' %hglen' Htyped Hgtyped Hpred
      ispecialize IH $$ %vs' %Φ
      iapply IH
      · ipureintro; omega
      · inext
        iexists ρ
        iexists gs'
        iframe
        ipureintro
        exact ⟨hagr', hglen'⟩
    icases Hpre with ⟨%ρ, %gs, %hagr0, %hglen0, Htyped0, Hgtyped0, Hpred0⟩
    ispecialize HR $$ %ρ %vs %gs %P
    ispecialize HR $$ [] [] Htyped0 Hgtyped0 Hpred0
    · ipureintro
      exact hagr0
    · ipureintro
      exact hglen0
    iexact HR
  · unfold isPrecondFor
    iintro #Hfix
    imodintro
    iintro %ρ %Φ %vs %gs %hagr %hlen %hglen Htyped Hgtyped Hpred
    ispecialize Hfix $$ %vs %Φ
    iapply Hfix
    · ipureintro; omega
    · inext
      iexists ρ
      iexists gs
      iframe
      ipureintro
      exact ⟨hagr, hglen⟩
end Precondition

/-! ## Well-Formedness Proofs -/
section WellFormedness

omit [MicaGS HasLC.hasLC Sig] in
theorem checkWf_ok {spec : Spec TinyML.Typ} {Δ : Signature}
    (h : spec.checkWf Δ = .ok ()) : spec.wfIn Δ :=
  PredTrans.checkWf_ok h

omit [MicaGS HasLC.hasLC Sig] in
theorem wfIn_mono {spec : Spec TinyML.Typ} {Δ Δ' : Signature}
    (h : spec.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) :
    spec.wfIn Δ' :=
  PredTrans.wfIn_mono h (Signature.Subset.declVars hsub (argVars spec.allArgs))
    (Signature.wf_declVars hwf)

end WellFormedness

/-! ## Environment Agreement -/
section EnvironmentAgreement

omit [MicaGS HasLC.hasLC Sig] in
/-- `argsEnv` preserves `agreeOn`: if two envs agree on `Δ`,
    then after applying the same updates, they agree on `argVars args ++ Δ`. -/
theorem argsEnv_agreeOn {Δ : Signature} {ρ₁ ρ₂ : Env}
    (h : Env.agreeOn Δ ρ₁ ρ₂) :
    ∀ (args : List String) (vals : List Runtime.Val),
    args.length ≤ vals.length →
    Env.agreeOn (Δ.declVars (argVars args))
      (argsEnv ρ₁ args vals) (argsEnv ρ₂ args vals) := by
  intro args
  induction args generalizing Δ ρ₁ ρ₂ with
  | nil => intro vals _; simp only [argVars, List.map, argsEnv, Signature.declVars]; exact h
  | cons name rest ih =>
    intro vals hlen
    cases vals with
    | nil => simp at hlen
    | cons v vs =>
      simp only [argsEnv, argVars, List.map]
      simpa [Signature.declVars] using
        ih (Env.agreeOn_declVar h) vs (by simp [List.length] at hlen ⊢; omega)

end EnvironmentAgreement

/-! ## Call Protocol Correctness -/
section CallCorrectness

omit [MicaGS HasLC.hasLC Sig] in
/-- Correctness of `declareArgs`: after processing all arguments, the resulting
    substitution is well-formed, types match, and the env agrees with `argsEnv`. -/
theorem declareArgs_correct :
    ∀ (argNames : List String) (argTys : List TinyML.Typ)
      (sargs : List (TinyML.Typ × Term .value))
      (Δ_base : Signature) (σ : FiniteSubst) (st : TransState) (ρ : Env)
      (Ψ : FiniteSubst → TransState → Env → Prop),
    argNames.length = argTys.length →
    σ.wfIn Δ_base st.decls →
    (∀ p ∈ sargs, (p : TinyML.Typ × Term .value).2.wfIn st.decls) →
    VerifM.eval (Spec.declareArgs σ argNames argTys sargs) st ρ Ψ →
    ∃ σ' st' ρ', Ψ σ' st' ρ' ∧
      σ'.wfIn Δ_base st'.decls ∧
      st'.owns = st.owns ∧
      sargs.map Prod.fst = argTys ∧
      ((Δ_base.declVars σ.dom).declVars (Spec.argVars argNames)).Subset
        (Δ_base.declVars σ'.dom) ∧
      Env.agreeOn ((Δ_base.declVars σ.dom).declVars (Spec.argVars argNames))
        ((σ'.subst.eval ρ'))
        (Spec.argsEnv ((σ.subst.eval ρ)) argNames
          (sargs.map fun p => p.2.eval ρ)) := by
  intro argNames
  induction argNames with
  | nil =>
    intro argTys sargs Δ_base σ st ρ Ψ hlen hσwf _ heval
    cases argTys with
    | cons _ _ => simp at hlen
    | nil =>
    cases sargs with
    | nil =>
      simp [Spec.declareArgs] at heval
      exact ⟨σ, st, ρ, VerifM.eval_ret heval, hσwf, rfl, rfl, Signature.Subset.refl _,
        by simp [Spec.argVars, Spec.argsEnv]; exact Env.agreeOn_refl⟩
    | cons _ _ =>
      simp [Spec.declareArgs] at heval
      exact (VerifM.eval_fatal heval).elim
  | cons name rest ih =>
    intro argTys sargs Δ_base σ st ρ Ψ hlen hσwf hsargs heval
    cases argTys with
    | nil => simp at hlen
    | cons ty tys =>
    have hlen_rest : rest.length = tys.length := by simpa using hlen
    cases sargs with
    | nil =>
      simp [Spec.declareArgs] at heval
      exact (VerifM.eval_fatal heval).elim
    | cons sarg_hd sargs_rest =>
      obtain ⟨targ, sarg⟩ := sarg_hd
      simp only [Spec.declareArgs] at heval
      by_cases hsub_ty : targ = ty
      · simp [hsub_ty] at heval
        have hdecl := VerifM.eval_decl
          (VerifM.eval_bind (VerifM.eval_ret (VerifM.eval_bind heval)))
        set argVar := st.freshConst (some name) .value
        set σ' := σ.rename ⟨name, .value⟩ argVar.name
        set ρ₁ := ρ.updateConst .value argVar.name (sarg.eval ρ)
        have hstwf : st.decls.wf := hσwf.useWf
        obtain ⟨hfresh_decls, hfresh_range, hrename⟩ :=
          FiniteSubst.rename_freshConst hσwf ⟨name, .value⟩
        have hσ'wf : σ'.wfIn Δ_base (st.decls.addConst argVar) := by
          simpa [σ', argVar] using hrename
        have hsarg_wf : sarg.wfIn st.decls := hsargs _ (List.mem_cons_self ..)
        have hassume := VerifM.eval_assumePure
          (VerifM.eval_bind (hdecl (sarg.eval ρ)))
          (by
            simpa [argVar] using
              (Formula.eq_wfIn_addConst_of_fresh
                (Δ := st.decls) (c := argVar) hstwf hsarg_wf hfresh_decls))
          (by
            simpa [argVar] using
              (Formula.eq_eval_updateConst_of_fresh
                (Δ := st.decls) (ρ := ρ) (c := argVar) hsarg_wf hfresh_decls))
        have hstwf_add : (st.decls.addConst argVar).wf := Signature.wf_addConst hstwf hfresh_decls
        have hsargs_rest : ∀ p ∈ sargs_rest, (p : TinyML.Typ × Term .value).2.wfIn
            (st.decls.addConst argVar) := fun p hp =>
          Term.wfIn_mono _ (hsargs p (List.mem_cons_of_mem _ hp))
            (Signature.Subset.subset_addConst _ _) hstwf_add
        have hsargs_eval : sargs_rest.map (fun p => p.2.eval ρ₁) =
            sargs_rest.map (fun p => p.2.eval ρ) :=
          List.map_congr_left fun p hp => Term.eval_env_agree
            (hsargs p (List.mem_cons_of_mem _ hp))
            (Env.agreeOn_symm (Env.agreeOn_update_fresh_const hfresh_decls))
        obtain ⟨σ'', st'', ρ'', hΨ, hσ''wf, howns, hsublist, hdom_sub, hagree⟩ :=
          ih tys sargs_rest Δ_base σ' _ ρ₁ Ψ hlen_rest hσ'wf hsargs_rest hassume
        refine ⟨σ'', st'', ρ'', hΨ, hσ''wf, howns,
          by simp [hsub_ty, hsublist], ?_, ?_⟩
        · change (((Δ_base.declVars σ.dom).declVar ⟨name, .value⟩).declVars
              (Spec.argVars rest)).Subset (Δ_base.declVars σ''.dom)
          simpa [σ', FiniteSubst.rename_source_eq] using hdom_sub
        · have hlen : rest.length ≤ sargs_rest.length := by
            have := congrArg List.length hsublist
            simp [List.length_map] at this; omega
          have hag_rename := FiniteSubst.rename_agreeOn
            (σ := σ) (Δ_base := Δ_base) (Δ_use := st.decls)
            (v := ⟨name, .value⟩) (name' := argVar.name)
            (ρ := ρ) (u := sarg.eval ρ) hσwf hfresh_range
          have hag_env := Spec.argsEnv_agreeOn
            (ρ₁ := (σ'.subst.eval ρ₁))
            (ρ₂ := ((σ.subst.eval ρ).updateConst .value name (sarg.eval ρ)))
            (by simpa [Env.agreeOn, σ', ] using hag_rename)
            rest (sargs_rest.map fun p => p.2.eval ρ) (by simp [List.length_map]; omega)
          rw [hsargs_eval] at hagree
          change Env.agreeOn
            (((Δ_base.declVars σ.dom).declVar ⟨name, .value⟩).declVars (Spec.argVars rest))
            ((σ''.subst.eval ρ''))
            (Spec.argsEnv (((σ.subst.eval ρ)).updateConst
              .value name (sarg.eval ρ)) rest
              (sargs_rest.map fun p => p.2.eval ρ))
          simpa [σ', FiniteSubst.rename_source_eq, Spec.argsEnv,             Env.agreeOn] using
            (Env.agreeOn_trans hagree hag_env)
      · simp [hsub_ty] at heval
        exact (VerifM.eval_fatal (VerifM.eval_bind heval)).elim

theorem call_correct (W : TinyML.World)
    (argTys : List TinyML.Typ) (retTy : TinyML.Typ) (s : Spec TinyML.Typ) (Δ_base : Signature)
    (σ : FiniteSubst) (sargs sgargs : List (TinyML.Typ × Term .value))
    (st : TransState) (ρ : Env)
    (Ψ : (TinyML.Typ × Term .value) → TransState → Env → Prop)
    (Φ : Runtime.Val → iProp) (R : iProp) :
    s.args.length = argTys.length →
    PredTrans.wfIn ((Δ_base.declVars σ.dom).declVars (Spec.argVars s.allArgs)) s.pred →
    σ.wfIn Δ_base st.decls →
    (∀ p ∈ sargs, (p : TinyML.Typ × Term .value).2.wfIn st.decls) →
    (∀ p ∈ sgargs, (p : TinyML.Typ × Term .value).2.wfIn st.decls) →
    VerifM.eval (Spec.call σ argTys retTy s sargs sgargs) st ρ Ψ →
    (∀ v st' ρ' t, Ψ (retTy, t) st' ρ' → t.wfIn st'.decls → t.eval ρ' = v →
      st'.sl W ρ' ∗ R ∗ TinyML.ValHasType W v retTy ⊢ Φ v) →
    sargs.map Prod.fst = argTys ∧ sgargs.map Prod.fst = s.ghost.map Prod.snd ∧
    (st.sl W ρ ∗ R ⊢ PredTrans.apply (TinyML.ValHasType W) (fun r => TinyML.ValHasType W r retTy -∗ Φ r) s.pred
      (Spec.argsEnv ((σ.subst.eval ρ)) s.allArgs
        ((sargs.map fun p => p.2.eval ρ) ++ (sgargs.map fun p => p.2.eval ρ)))) := by
  intro hlen hwf hσwf hsargs hsgargs heval hΨ
  simp only [Spec.call] at heval
  have hb_grow := VerifM.eval.decls_grow ρ (VerifM.eval_bind heval)
  obtain ⟨σ₁, st₁, ρ₁, ⟨hdsub₁, hragree₁, hΨ₁⟩, hσ₁wf, howns₁, hsublist, hdom_sub₁, hagree₁⟩ :=
    declareArgs_correct s.args argTys sargs Δ_base σ st ρ _ hlen hσwf hsargs hb_grow
  have hst₁wf : st₁.decls.wf := hσ₁wf.useWf
  have hsgargs₁ : ∀ p ∈ sgargs, (p : TinyML.Typ × Term .value).2.wfIn st₁.decls :=
    fun p hp => Term.wfIn_mono _ (hsgargs p hp) hdsub₁ hst₁wf
  have hsgargs_eval : sgargs.map (fun p => p.2.eval ρ₁) = sgargs.map (fun p => p.2.eval ρ) :=
    List.map_congr_left fun p hp =>
      Term.eval_env_agree (hsgargs p hp) (Env.agreeOn_symm hragree₁)
  have hb_grow₂ := VerifM.eval.decls_grow ρ₁ (VerifM.eval_bind hΨ₁)
  obtain ⟨σ', st', ρ', ⟨hdsub₂, hragree₂, hΨ'⟩, hσ'wf, howns₂, hsublist₂, hdom_sub₂, hagree₂⟩ :=
    declareArgs_correct (s.ghost.map Prod.fst) (s.ghost.map Prod.snd) sgargs Δ_base σ₁ st₁ ρ₁ _
      (by simp) hσ₁wf hsgargs₁ hb_grow₂
  refine ⟨hsublist, hsublist₂, ?_⟩
  have howns : st'.owns = st.owns := howns₂.trans howns₁
  have hragree : Env.agreeOn st.decls ρ ρ' :=
    Env.agreeOn_trans hragree₁ (Env.agreeOn_mono hdsub₁ hragree₂)
  have hdecl_split : (Δ_base.declVars σ.dom).declVars (Spec.argVars s.allArgs)
      = ((Δ_base.declVars σ.dom).declVars (Spec.argVars s.args)).declVars
          (Spec.argVars (s.ghost.map Prod.fst)) := by
    simp [Spec.argVars, Spec.allArgs, Signature.declVars, List.foldl_append]
  have hargsEnv_split : Spec.argsEnv ((σ.subst.eval ρ)) s.allArgs
        ((sargs.map fun p => p.2.eval ρ) ++ (sgargs.map fun p => p.2.eval ρ))
      = Spec.argsEnv (Spec.argsEnv ((σ.subst.eval ρ)) s.args (sargs.map fun p => p.2.eval ρ))
          (s.ghost.map Prod.fst) (sgargs.map fun p => p.2.eval ρ) := by
    refine Spec.argsEnv_append _ _ _ _ _ ?_
    have := congrArg List.length hsublist
    simp [List.length_map] at this ⊢; omega
  have hagree : Env.agreeOn ((Δ_base.declVars σ.dom).declVars (Spec.argVars s.allArgs))
      ((σ'.subst.eval ρ'))
      (Spec.argsEnv ((σ.subst.eval ρ)) s.allArgs
        ((sargs.map fun p => p.2.eval ρ) ++ (sgargs.map fun p => p.2.eval ρ))) := by
    have hstep := Spec.argsEnv_agreeOn hagree₁ (s.ghost.map Prod.fst)
      (sgargs.map fun p => p.2.eval ρ) (by
        have := congrArg List.length hsublist₂
        simp [List.length_map] at this ⊢; omega)
    rw [hsgargs_eval] at hagree₂
    rw [hdecl_split, hargsEnv_split]
    exact Env.agreeOn_trans (Env.agreeOn_mono
      (Signature.Subset.declVars hdom_sub₁ (Spec.argVars (s.ghost.map Prod.fst))) hagree₂) hstep
  have hwf'' : PredTrans.wfIn (Δ_base.declVars σ'.dom) s.pred :=
    PredTrans.wfIn_mono (hdecl_split ▸ hwf)
      ((hdom_sub₁.declVars _).trans hdom_sub₂) hσ'wf.srcWf
  have hcall := PredTrans.call_correct W s.pred Δ_base σ' st' ρ'
    _ (fun r => TinyML.ValHasType W r retTy -∗ Φ r) R
    hwf'' hσ'wf (VerifM.eval_bind hΨ')
    (fun v st'' ρ'' t hΨ'' htwf hteval => by
      apply wand_intro
      iintro ⟨⟨Howns, HR⟩, Hty⟩
      iintuitionistic Hty
      ihave Hpure := (TinyML.typeConstraints_hold (ty := retTy) (t := t) (ρ := ρ'') (W := W) (v := v) hteval) $$ Hty
      ipure Hpure
      obtain ⟨st₃, hst₃_decls, hst₃_owns, _, hret⟩ :=
        VerifM.eval_assumeAll (VerifM.eval_bind hΨ'')
          (fun φ hφ => TinyML.typeConstraints_wfIn htwf φ hφ)
          (fun φ hφ => Hpure φ hφ)
      ihave Harg : (st₃.sl W ρ'' ∗ R ∗ TinyML.ValHasType W v retTy) $$ [HR Howns Hty]
      · iframe HR Hty
        simp [TransState.sl, hst₃_owns]; iassumption
      iapply (hΨ v st₃ ρ'' t (VerifM.eval_ret hret) (hst₃_decls ▸ htwf) hteval) $$ Harg)
  exact (sep_mono_left (SpatialContext.interp_env_agree W (VerifM.eval.wf heval).ownsWf hragree).1).trans <|
    (by simpa [howns] using hcall : st.sl W ρ' ∗ R ⊢ _).trans <|
    PredTrans.apply_env_agree (TinyML.ValHasType W) hwf hagree

end CallCorrectness

/-! ## Implementation Protocol Correctness -/
section ImplementCorrectness

/-- Correctness payload for `declareImplArgs`. -/
def DeclareImplArgs.Result (argNames : List String) (vs : List Runtime.Val)
    (Δ_base : Signature) (σ : FiniteSubst) (st : TransState) (ρ : Env)
    (Ψ : (FiniteSubst × List FOL.Const) → TransState → Env → Prop) : Prop :=
  ∃ σ' implVars st' ρ', Ψ (σ', implVars) st' ρ' ∧
    σ'.wfIn Δ_base st'.decls ∧
    st.decls.Subset st'.decls ∧
    Env.agreeOn st.decls ρ ρ' ∧
    st'.owns = st.owns ∧
    ((Δ_base.declVars σ.dom).declVars (argVars argNames)).Subset
      (Δ_base.declVars σ'.dom) ∧
    Env.agreeOn ((Δ_base.declVars σ.dom).declVars (argVars argNames))
      ((σ'.subst.eval ρ'))
      (argsEnv ((σ.subst.eval ρ)) argNames vs) ∧
    (∀ v ∈ implVars, v ∈ st'.decls.consts) ∧
    (∀ v ∈ implVars, v.sort = .value) ∧
    Terms.Eval ρ' (implVars.map (fun av => .const (.uninterpreted av.name .value))) vs

theorem declareImplArgs_correct (W : TinyML.World) :
    ∀ (argNames : List String) (argTys : List TinyML.Typ) (vs : List Runtime.Val)
      (Δ_base : Signature) (σ : FiniteSubst) (st : TransState) (ρ : Env)
      (Ψ : (FiniteSubst × List FOL.Const) → TransState → Env → Prop),
    argNames.length = argTys.length →
    σ.wfIn Δ_base st.decls →
    VerifM.eval (Spec.declareImplArgs σ argNames argTys) st ρ Ψ →
    TinyML.ValsHaveTypes W vs argTys ⊢
      ⌜Spec.DeclareImplArgs.Result argNames vs Δ_base σ st ρ Ψ⌝ := by
  intro argNames
  induction argNames with
  | nil =>
    intro argTys vs Δ_base σ st ρ Ψ hlen_names hσwf heval
    cases argTys with
    | cons _ _ => simp at hlen_names
    | nil =>
    iintro Hvs
    ihave %hlen := TinyML.ValsHaveTypes.length_eq $$ Hvs
    cases vs with
    | nil =>
      simp [Spec.declareImplArgs] at heval
      have := VerifM.eval_ret heval
      ipureintro
      exact ⟨σ, [], st, ρ, this, hσwf,
        Signature.Subset.refl _, Env.agreeOn_refl, rfl, Signature.Subset.refl _,
        by simp [Spec.argVars, Spec.argsEnv]; exact Env.agreeOn_refl,
        nofun,
        nofun,
        .nil⟩
    | cons _ _ =>
      simp at hlen
  | cons name rest ih =>
    intro argTys vs Δ_base σ st ρ Ψ hlen_names hσwf heval
    cases argTys with
    | nil => simp at hlen_names
    | cons ty tys =>
    have hlen_rest_names : rest.length = tys.length := by simpa using hlen_names
    cases vs with
    | nil =>
      exact (TinyML.ValsHaveTypes.nil_cons W ty tys).1.trans false_elim
    | cons v vs' =>
      refine (TinyML.ValsHaveTypes.cons W v vs' ty tys).1.trans ?_
      iintro Hvs
      icases Hvs with ⟨Hv, Hvs_rest⟩
      simp only [Spec.declareImplArgs] at heval
      have hdecl := VerifM.eval_decl (VerifM.eval_bind heval)
      set argVar := st.freshConst (some name) .value
      set σ' := σ.rename ⟨name, .value⟩ argVar.name
      set ρ₁ := ρ.updateConst .value argVar.name v
      specialize hdecl v
      have hstwf : st.decls.wf := hσwf.useWf
      obtain ⟨hfresh_decls, hfresh_range, hrename⟩ :=
        FiniteSubst.rename_freshConst hσwf ⟨name, .value⟩
      have hσ'wf : σ'.wfIn Δ_base (st.decls.addConst argVar) := by
        simpa [σ', argVar] using hrename
      have hvar_wf : (Term.const (.uninterpreted argVar.name .value)).wfIn (st.decls.addConst argVar) := by
        simpa using
          (Term.const_wfIn_addConst_of_fresh (Δ := st.decls) (c := argVar) hstwf hfresh_decls)
      have hvar_eval : (Term.const (.uninterpreted argVar.name .value)).eval ρ₁ = v := by
        simp [ρ₁]
      ihave %htyped_formulas := TinyML.typeConstraints_hold (ty := ty)
          (t := .const (.uninterpreted argVar.name .value))
          (ρ := ρ₁) (W := W) (v := v) hvar_eval $$ Hv
      obtain ⟨st₂, hst₂_decls, hst₂_owns, _, hdecl₂⟩ :=
        VerifM.eval_assumeAll (VerifM.eval_bind hdecl)
          (fun φ hφ => TinyML.typeConstraints_wfIn hvar_wf φ hφ)
          (fun φ hφ => htyped_formulas φ hφ)
      have hst_st₂ : st.decls.Subset st₂.decls :=
        hst₂_decls ▸ Signature.Subset.subset_addConst _ _
      ihave %hih := ih tys vs' Δ_base σ' st₂ ρ₁
        (fun p st' ρ' => Ψ (p.1, argVar :: p.2) st' ρ')
        hlen_rest_names
        (hst₂_decls ▸ hσ'wf)
        ((VerifM.eval_bind hdecl₂).mono (fun _ _ _ hp => VerifM.eval_ret hp))
        $$ Hvs_rest
      obtain ⟨σ'', argVars', st', ρ', hΨ, hσ''wf, hdsub', hragree',
        howns, hdom_sub, hagree, hmem_decls, hsorts, hlookups⟩ := hih
      ihave %hlen_rest := TinyML.ValsHaveTypes.length_eq $$ Hvs_rest
      have hag_rename := FiniteSubst.rename_agreeOn
        (σ := σ) (Δ_base := Δ_base) (Δ_use := st.decls)
        (v := ⟨name, .value⟩) (name' := argVar.name)
        (ρ := ρ) (u := v) hσwf hfresh_range
      have hag_env := Spec.argsEnv_agreeOn
        (ρ₁ := (σ'.subst.eval ρ₁))
        (ρ₂ := ((σ.subst.eval ρ).updateConst .value name v))
        (by simpa [Env.agreeOn, σ'] using hag_rename)
        rest vs' (by omega)
      ipureintro
      refine ⟨σ'', argVar :: argVars', st', ρ', hΨ, hσ''wf,
        Signature.Subset.trans hst_st₂ hdsub',
        Env.agreeOn_trans
          (Env.agreeOn_update_fresh_const (ρ := ρ) (c := argVar) (u := v) hfresh_decls)
          (Env.agreeOn_mono hst_st₂ hragree'),
        howns.trans hst₂_owns, ?_, ?_, ?_, ?_, ?_⟩
      · change (((Δ_base.declVars σ.dom).declVar ⟨name, .value⟩).declVars
            (Spec.argVars rest)).Subset (Δ_base.declVars σ''.dom)
        simpa [σ', FiniteSubst.rename_source_eq] using hdom_sub
      · change Env.agreeOn
          (((Δ_base.declVars σ.dom).declVar ⟨name, .value⟩).declVars (Spec.argVars rest))
          ((σ''.subst.eval ρ'))
          (Spec.argsEnv (((σ.subst.eval ρ)).updateConst .value name v)
            rest vs')
        simpa [σ', FiniteSubst.rename_source_eq, Spec.argsEnv,           Env.agreeOn] using
          (Env.agreeOn_trans hagree hag_env)
      · intro w hw
        cases List.mem_cons.mp hw with
        | inl h => subst h; exact hdsub'.consts argVar (hst₂_decls ▸ List.mem_cons_self ..)
        | inr h => exact hmem_decls w h
      · intro w hw
        cases List.mem_cons.mp hw with
        | inl h => subst h; rfl
        | inr h => exact hsorts w h
      · refine List.Forall₂.cons ?_ hlookups
        have h1 := hragree'.2.1 argVar (hst₂_decls ▸ List.mem_cons_self ..)
        have h1' : Term.eval ρ' (Term.const (.uninterpreted argVar.name .value)) =
            Term.eval ρ₁ (Term.const (.uninterpreted argVar.name .value)) := by
          simpa [Term.eval, Const.denote, Env.lookupConst] using h1.symm
        exact h1'.trans hvar_eval

theorem implement_correct (W : TinyML.World)
    (argTys : List TinyML.Typ) (retTy : TinyML.Typ) (s : Spec TinyML.Typ)
    (body : List FOL.Const → List FOL.Const → VerifM (Term .value))
    (st : TransState) (ρ : Env) (vs gs : List Runtime.Val)
    (Φ : Runtime.Val → iProp) (R : iProp) :
    s.args.length = argTys.length →
    s.ghost.length = gs.length →
    s.wfIn W.Δ_spec →
    W.wf →
    W.agrees st.decls ρ →
    VerifM.eval (Spec.implement W.Δ_spec argTys s body) st ρ (fun _ _ _ => True) →
    (∀ (argVars ghostVars : List FOL.Const) (st' : TransState) (ρ' : Env) (Q : iProp),
      st.decls.Subset st'.decls →
      Env.agreeOn st.decls ρ ρ' →
      (∀ v ∈ argVars, v ∈ st'.decls.consts) →
      (∀ v ∈ argVars, v.sort = .value) →
      List.Forall₂ (fun av val => ρ'.consts .value av.name = val) argVars vs →
      VerifM.eval (body argVars ghostVars) st' ρ'
        (fun result st'' ρ'' =>
          ∀ (S : iProp), result.wfIn st''.decls →
            st''.sl W ρ'' ∗ Q ∗ ((TinyML.ValHasType W (result.eval ρ'') retTy -∗ Φ (result.eval ρ'')) -∗ S) ⊢ S) →
      st'.sl W ρ' ∗ Q ⊢ R) →
    st.sl W ρ ∗ TinyML.ValsHaveTypes W vs argTys ∗
      TinyML.ValsHaveTypes W gs (s.ghost.map Prod.snd) ∗
      PredTrans.apply (TinyML.ValHasType W) (fun r => TinyML.ValHasType W r retTy -∗ Φ r) s.pred
        (Spec.argsEnv W.ρ_spec s.allArgs (vs ++ gs)) ⊢ R := by
  intro hlen hglen hswf hwf hag heval hbody
  simp only [Spec.implement] at heval
  have hb := VerifM.eval_bind heval
  iintro H
  icases H with ⟨Howns, Hvals, Hgvals, Happ⟩
  iintuitionistic Hvals
  iintuitionistic Hgvals
  ihave %hlen_vals := TinyML.ValsHaveTypes.length_eq $$ Hvals
  ihave Hdecl := declareImplArgs_correct W s.args argTys vs W.Δ_spec (FiniteSubst.base W.Δ_spec) st ρ _
      hlen
      (FiniteSubst.base_wfIn hag.subset hwf.wf (VerifM.eval.wf heval).namesDisjoint hwf.vars)
      hb $$ Hvals
  ipure Hdecl
  obtain ⟨σ₁, argVars, st₁, ρ₁, hΨ₁, hσ₁wf, hdsub₁, hragree₁, howns₁, hdom_sub₁, hagree₁,
    hmem_decls, hsorts, hlookups⟩ := Hdecl
  ihave Hgdecl := declareImplArgs_correct W (s.ghost.map Prod.fst) (s.ghost.map Prod.snd) gs
      W.Δ_spec σ₁ st₁ ρ₁ _ (by simp) hσ₁wf (VerifM.eval_bind hΨ₁) $$ Hgvals
  ipure Hgdecl
  obtain ⟨σ', ghostVars, st', ρ', hΨ, hσ'wf, hdsub₂, hragree₂, howns₂, hdom_sub₂, hagree₂,
    _, _, _⟩ := Hgdecl
  have hdsub : st.decls.Subset st'.decls := hdsub₁.trans hdsub₂
  have hragree : Env.agreeOn st.decls ρ ρ' :=
    Env.agreeOn_trans hragree₁ (Env.agreeOn_mono hdsub₁ hragree₂)
  have howns : st'.owns = st.owns := howns₂.trans howns₁
  have hdecl_split : W.Δ_spec.declVars (Spec.argVars s.allArgs)
      = (W.Δ_spec.declVars (Spec.argVars s.args)).declVars
          (Spec.argVars (s.ghost.map Prod.fst)) := by
    simp [Spec.argVars, Spec.allArgs, Signature.declVars, List.foldl_append]
  have hargsEnv_split : ∀ ρ₀ : Env, Spec.argsEnv ρ₀ s.allArgs (vs ++ gs)
      = Spec.argsEnv (Spec.argsEnv ρ₀ s.args vs) (s.ghost.map Prod.fst) gs := fun ρ₀ =>
    Spec.argsEnv_append _ _ _ _ _ (by omega)
  have hag_base :
      Env.agreeOn (W.Δ_spec.declVars (Spec.argVars s.allArgs))
        (Spec.argsEnv W.ρ_spec s.allArgs (vs ++ gs))
            (Spec.argsEnv (((FiniteSubst.base W.Δ_spec).subst.eval ρ)) s.allArgs (vs ++ gs)) :=
    Spec.argsEnv_agreeOn (Δ := W.Δ_spec)
      (ρ₁ := W.ρ_spec)
      (ρ₂ := ((FiniteSubst.base W.Δ_spec).subst.eval ρ))
      (by simpa [FiniteSubst.base, ] using hag.agree)
      s.allArgs (vs ++ gs)
      (by simp [Spec.allArgs]; omega)
  have hagree : Env.agreeOn (W.Δ_spec.declVars (Spec.argVars s.allArgs))
      ((σ'.subst.eval ρ'))
      (Spec.argsEnv (((FiniteSubst.base W.Δ_spec).subst.eval ρ)) s.allArgs (vs ++ gs)) := by
    have hstep := Spec.argsEnv_agreeOn hagree₁ (s.ghost.map Prod.fst) gs (by simp; omega)
    rw [hdecl_split, hargsEnv_split]
    refine Env.agreeOn_trans (Env.agreeOn_mono
      (Signature.Subset.declVars ?_ (Spec.argVars (s.ghost.map Prod.fst))) hagree₂) ?_
    · simpa [FiniteSubst.base, Signature.declVars] using hdom_sub₁
    · simpa [FiniteSubst.base, Signature.declVars] using hstep
  have hswf' : PredTrans.wfIn (((W.Δ_spec.declVars (FiniteSubst.base W.Δ_spec).dom).declVars
      (Spec.argVars s.args)).declVars (Spec.argVars (s.ghost.map Prod.fst))) s.pred := by
    have h := hswf
    unfold Spec.wfIn at h
    rw [hdecl_split] at h
    simpa [FiniteSubst.base, Signature.declVars] using h
  have hst'_wf : st'.decls.wf := (VerifM.eval.wf hΨ).namesDisjoint
  have hmem_decls' : ∀ v ∈ argVars, v ∈ st'.decls.consts :=
    fun v hv => hdsub₂.consts v (hmem_decls v hv)
  have hlookups' : List.Forall₂
      (fun t val => Term.eval ρ' t = val)
      (argVars.map (fun av => Term.const (.uninterpreted av.name .value))) vs := by
    refine Terms.Eval.env_agree (ρ := ρ₁) ?_ hragree₂ hlookups
    intro t ht
    obtain ⟨av, hav, rfl⟩ := List.mem_map.mp ht
    obtain ⟨_, _⟩ := av
    have hsort := hsorts _ hav
    cases hsort
    exact Term.const_wfIn_of_mem ((VerifM.eval.wf hΨ₁).namesDisjoint) (hmem_decls _ hav)
  iapply (show st'.sl W ρ' ∗
        PredTrans.apply (TinyML.ValHasType W) (fun r => TinyML.ValHasType W r retTy -∗ Φ r) s.pred
          ((σ'.subst.eval ρ')) ⊢ R from
    PredTrans.implement_correct W s.pred W.Δ_spec σ' (body argVars ghostVars) st' ρ'
      (fun r => TinyML.ValHasType W r retTy -∗ Φ r) R
      (PredTrans.wfIn_mono hswf' (hdom_sub₁.declVars _ |>.trans hdom_sub₂) hσ'wf.srcWf)
      hσ'wf hΨ
      (fun st'' ρ'' Q hdsub' hragree' hbody_eval => by
        apply hbody argVars ghostVars st'' ρ'' Q
          (hdsub.trans hdsub')
          (Env.agreeOn_trans hragree (Env.agreeOn_mono hdsub hragree'))
          (fun v hv => hdsub'.consts v (hmem_decls' v hv)) hsorts
        · refine Terms.Eval.lookup_const (Terms.Eval.env_agree (ρ := ρ') ?_ hragree' hlookups')
          intro t ht
          obtain ⟨av, hav, rfl⟩ := List.mem_map.mp ht
          obtain ⟨_, _⟩ := av
          have hsort := hsorts _ hav
          cases hsort
          exact Term.const_wfIn_of_mem hst'_wf (hmem_decls' _ hav)
        · exact hbody_eval))
  isplitr [Happ]
  · iapply (show st.sl W ρ' ⊢ st'.sl W ρ' by simp [howns, TransState.sl])
    iapply (show st.sl W ρ ⊢ st.sl W ρ' by
      simpa [TransState.sl] using
        (SpatialContext.interp_env_agree W (VerifM.eval.wf heval).ownsWf hragree).1)
    iexact Howns
  · iapply (PredTrans.apply_env_agree (TinyML.ValHasType W) hswf
      (Env.agreeOn_trans hag_base (Env.agreeOn_symm hagree)))
    iexact Happ

end ImplementCorrectness
end Spec

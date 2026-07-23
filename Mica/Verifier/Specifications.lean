-- SUMMARY: Function specifications, their semantics, and the protocols for specification calls and implementations.
import Mica.TinyML.Typed
import Mica.TinyML.Typing
import Mica.FOL.Printing
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

Defines `Spec` and its call/implementation operations built on top of
`PredTrans`.
-/

-- ---------------------------------------------------------------------------
-- Spec
-- ---------------------------------------------------------------------------

/-- A complete specification for a (possibly multi-argument) function, pairing the
    predicate transformer with the argument and return types from the function annotation. -/
structure Spec where
  args    : List (String × TinyML.Typ)
  retTy   : TinyML.Typ
  pred    : PredTrans
  deriving DecidableEq

namespace Spec

/-! ## Definitions -/

/-- The list of SMT variables corresponding to a spec's arguments. -/
def argVars (args : List (String × TinyML.Typ)) : List Var :=
  args.map fun (name, _) => ⟨name, .value⟩

/-- Instantiate a spec scheme: substitute `σ` into the argument and return
    types. The predicate transformer is untouched — a polymorphic intrinsic is a
    family of functions with the same implementation, so only the types vary
    with the instantiation. -/
def instantiate (s : Spec) (σ : TinyML.TyVar → TinyML.Typ) : Spec :=
  { args  := s.args.map fun (name, ty) => (name, ty.subst σ)
    retTy := s.retTy.subst σ
    pred  := s.pred }

omit [MicaGS HasLC.hasLC Sig] in
@[simp] theorem instantiate_pred (s : Spec) (σ : TinyML.TyVar → TinyML.Typ) :
    (s.instantiate σ).pred = s.pred := rfl

omit [MicaGS HasLC.hasLC Sig] in
@[simp] theorem instantiate_retTy (s : Spec) (σ : TinyML.TyVar → TinyML.Typ) :
    (s.instantiate σ).retTy = s.retTy.subst σ := rfl

omit [MicaGS HasLC.hasLC Sig] in
/-- Instantiation preserves argument names, hence the argument variables. -/
@[simp] theorem instantiate_argVars (s : Spec) (σ : TinyML.TyVar → TinyML.Typ) :
    argVars (s.instantiate σ).args = argVars s.args := by
  simp only [instantiate, argVars, List.map_map]
  rfl

/-- Build an environment binding each argument name to its value, left-to-right.
    Later arguments shadow earlier ones with the same name. -/
def argsEnv (ρ : VerifM.Env) : List (String × TinyML.Typ) → List Runtime.Val → VerifM.Env
  | [], _ | _, [] => ρ
  | (name, _) :: rest, v :: vs => argsEnv (ρ.updateConst .value name v) rest vs

def isPrecondFor (W : TinyML.World) (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (f : Runtime.Val) (s : Spec) : iProp :=
  iprop(□ ∀ (ρ : VerifM.Env) (Φ : Runtime.Val → iProp) (vs : List Runtime.Val),
      ⌜VerifM.Env.agreeOn Δ_spec ρ_spec ρ⌝ -∗
      TinyML.ValsHaveTypes W vs (s.args.map Prod.snd) -∗
        PredTrans.apply W (fun r => TinyML.ValHasType W r s.retTy -∗ Φ r) s.pred
          (argsEnv ρ s.args vs) -∗
        wp W.pctx (Runtime.Expr.app (.val f) (vs.map fun v => .val v)) Φ)

/-- A spec is well-formed when its predicate transformer is well-formed in the
    context extended with all argument variables. -/
def wfIn (spec : Spec) (Δ : Signature) : Prop :=
  PredTrans.wfIn (Δ.declVars (argVars spec.args)) spec.pred

def checkWf (spec : Spec) (Δ : Signature) : Except String Unit :=
  PredTrans.checkWf (Δ.declVars (argVars spec.args)) spec.pred

/-- Declare argument variables, check types, and assume equalities for a spec call.
    Returns the updated substitution. -/
def declareArgs (Θ : TinyML.TypeEnv) (σ : FiniteSubst) :
    List (String × TinyML.Typ) → List (TinyML.Typ × Term .value) → VerifM FiniteSubst
  | [], [] => pure σ
  | (name, ty) :: rest, (targ, sarg) :: sargs => do
    if TinyML.Typ.sub Θ targ ty then pure ()
    else VerifM.fatal s!"type mismatch in call to spec"
    let argVar ← VerifM.decl (some name) .value
    let σ' := σ.rename ⟨name, .value⟩ argVar.name
    VerifM.assume (.pure (.eq .value (.const (.uninterpreted argVar.name .value)) sarg))
    declareArgs Θ σ' rest sargs
  | _, _ => VerifM.fatal "wrong number of arguments"

/-- Full call protocol for a spec: declare argument variables, assume they equal the
    compiled argument terms, check argument types, then invoke `PredTrans.call`. -/
def call (Θ : TinyML.TypeEnv) (σ : FiniteSubst) (s : Spec) (sargs : List (TinyML.Typ × Term .value)) :
    VerifM (TinyML.Typ × Term .value) := do
  let σ' ← declareArgs Θ σ s.args sargs
  let result ← PredTrans.call σ' s.pred
  VerifM.assumeAll (TinyML.typeConstraints s.retTy result)
  pure (s.retTy, result)

/-- Declare implementation argument variables: for each `(name, ty)` in `args`,
    declare a fresh variable, assume its type constraints, and rename in `σ`.
    Returns the final substitution and the list of declared argument variables. -/
def declareImplArgs (σ : FiniteSubst) :
    List (String × TinyML.Typ) → VerifM (FiniteSubst × List FOL.Const)
  | [] => pure (σ, [])
  | (name, ty) :: rest => do
    let argVar ← VerifM.decl (some name) .value
    VerifM.assumeAll (TinyML.typeConstraints ty (.const (.uninterpreted argVar.name .value)))
    let σ' := σ.rename ⟨name, .value⟩ argVar.name
    let (σ'', vars) ← declareImplArgs σ' rest
    pure (σ'', argVar :: vars)

/-- Full implementation protocol for a spec: declare argument variables,
    assume type constraints, then invoke `PredTrans.implement`. Dual to `call`. -/
def implement (Δ_base : Signature) (s : Spec) (body : List FOL.Const → VerifM (Term .value)) : VerifM Unit := do
  let (σ, argVars) ← declareImplArgs (FiniteSubst.base Δ_base) s.args
  PredTrans.implement σ s.pred (body argVars)

/-! ## Precondition Proofs -/
section Precondition

instance : Iris.BI.Persistent (isPrecondFor W Δ_spec ρ_spec f s) := by
  unfold isPrecondFor
  infer_instance

/-- Fold `wp_fix'`'s tupled recursive obligation into a spec precondition;
    the two differ only by currying the typing hypothesis and the predicate transformer. -/
theorem isPrecondFor_intro (W : TinyML.World) (Δ_spec : Signature) (ρ_spec : VerifM.Env) (s : Spec)
    (f : Runtime.Val) :
    iprop(□ ∀ (ρ : VerifM.Env) (vs : List Runtime.Val) (P : Runtime.Val → iProp),
      (⌜VerifM.Env.agreeOn Δ_spec ρ_spec ρ⌝ ∗
        TinyML.ValsHaveTypes W vs (s.args.map Prod.snd) ∗
        PredTrans.apply W (fun r => TinyML.ValHasType W r s.retTy -∗ P r) s.pred
          (argsEnv ρ s.args vs)) -∗
        wp W.pctx (Runtime.Expr.app (.val f) (vs.map Runtime.Expr.val)) P) ⊢ s.isPrecondFor W Δ_spec ρ_spec f := by
  unfold isPrecondFor
  iintro #H
  imodintro
  iintro %ρ %Φ %vs Hagree Htyped Hpred
  ispecialize H $$ %ρ %vs %Φ
  iapply H
  iframe

/-- Löb-style rule for spec preconditions on `fix`: to prove
    `s.isPrecondFor W (.fix f args e)`, assume it as the recursive hypothesis and
    prove the `wp` of the body (after the usual fix-substitution). -/
theorem isPrecondFor_fix {W : TinyML.World} {Δ_spec : Signature} {ρ_spec : VerifM.Env} {s : Spec}
    {f : Runtime.Binder} {args : List Runtime.Binder} {e : Runtime.Expr}
    {R : iProp}
    (hargs : args.length = s.args.length)
    (h : R ⊢ □ (s.isPrecondFor W Δ_spec ρ_spec (.fix f args e) -∗
        ∀ (ρ : VerifM.Env) (vs : List Runtime.Val) (P : Runtime.Val → iProp),
          ⌜VerifM.Env.agreeOn Δ_spec ρ_spec ρ⌝ -∗
          TinyML.ValsHaveTypes W vs (s.args.map Prod.snd) -∗
          PredTrans.apply W (fun r => TinyML.ValHasType W r s.retTy -∗ P r) s.pred
              (argsEnv ρ s.args vs) -∗
          wp W.pctx (e.subst ((Runtime.Subst.id.updateBinder f (.fix f args e)).updateAllBinder args vs)) P)) :
    R ⊢ s.isPrecondFor W Δ_spec ρ_spec (.fix f args e) := by
  refine (SpatialContext.wp_fix' (pctx := W.pctx) (f := f) (args := args) (e := e) (Φ := fun P vs =>
      iprop(∃ ρ : VerifM.Env,
        ⌜VerifM.Env.agreeOn Δ_spec ρ_spec ρ⌝ ∗
          TinyML.ValsHaveTypes W vs (s.args.map Prod.snd) ∗
          PredTrans.apply W (fun r => TinyML.ValHasType W r s.retTy -∗ P r) s.pred
            (argsEnv ρ s.args vs))) ?_ (h.trans ?_)).trans ?_
  · intro vs P
    istart
    iintro ⟨%ρ, %hagr, Htyped, -⟩
    ihave %Hlen := TinyML.ValsHaveTypes.length_eq $$ Htyped
    ipureintro
    simp at Hlen
    omega
  · istart
    iintro #HR
    imodintro
    iintro #IH %vs %P Hpre
    ispecialize HR $$ [IH]
    · unfold isPrecondFor
      imodintro
      iintro %ρ %Φ %vs Hagree Htyped Hpred
      ispecialize IH $$ %vs %Φ
      iapply IH
      iexists ρ
      iframe
    icases Hpre with ⟨%ρ, %hagr0, #Htyped0, Hpred0⟩
    ispecialize HR $$ %ρ %vs %P
    iapply HR
    · ipureintro
      exact hagr0
    · iexact Htyped0
    · iexact Hpred0
  · unfold isPrecondFor
    iintro #Hfix
    imodintro
    iintro %ρ %Φ %vs Hagree Htyped Hpred
    ispecialize Hfix $$ %vs %Φ
    iapply Hfix
    iexists ρ
    iframe
end Precondition

/-! ## Well-Formedness Proofs -/
section WellFormedness

omit [MicaGS HasLC.hasLC Sig] in
theorem checkWf_ok {spec : Spec} {Δ : Signature}
    (h : spec.checkWf Δ = .ok ()) : spec.wfIn Δ :=
  PredTrans.checkWf_ok h

omit [MicaGS HasLC.hasLC Sig] in
theorem wfIn_mono {spec : Spec} {Δ Δ' : Signature}
    (h : spec.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) :
    spec.wfIn Δ' :=
  PredTrans.wfIn_mono h (Signature.Subset.declVars hsub (argVars spec.args))
    (Signature.wf_declVars hwf)

end WellFormedness

/-! ## Environment Agreement -/
section EnvironmentAgreement

omit [MicaGS HasLC.hasLC Sig] in
/-- `argsEnv` preserves `agreeOn`: if two envs agree on `Δ`,
    then after applying the same updates, they agree on `argVars args ++ Δ`. -/
theorem argsEnv_agreeOn {Δ : Signature} {ρ₁ ρ₂ : VerifM.Env}
    (h : VerifM.Env.agreeOn Δ ρ₁ ρ₂) :
    ∀ (args : List (String × TinyML.Typ)) (vals : List Runtime.Val),
    args.length ≤ vals.length →
    VerifM.Env.agreeOn (Δ.declVars (argVars args))
      (argsEnv ρ₁ args vals) (argsEnv ρ₂ args vals) := by
  intro args
  induction args generalizing Δ ρ₁ ρ₂ with
  | nil => intro vals _; simp only [argVars, List.map, argsEnv, Signature.declVars]; exact h
  | cons arg rest ih =>
    intro vals hlen
    obtain ⟨name, ty⟩ := arg
    cases vals with
    | nil => simp at hlen
    | cons v vs =>
      simp only [argsEnv, argVars, List.map]
      simpa [Signature.declVars] using
        ih (VerifM.Env.agreeOn_declVar h) vs (by simp [List.length] at hlen ⊢; omega)

end EnvironmentAgreement

/-! ## Call Protocol Correctness -/
section CallCorrectness

omit [MicaGS HasLC.hasLC Sig] in
/-- Correctness of `declareArgs`: after processing all arguments, the resulting
    substitution is well-formed, types match, and the env agrees with `argsEnv`. -/
theorem declareArgs_correct (W : TinyML.World) :
    ∀ (args : List (String × TinyML.Typ)) (sargs : List (TinyML.Typ × Term .value))
      (Δ_base : Signature) (σ : FiniteSubst) (st : TransState) (ρ : VerifM.Env)
      (Ψ : FiniteSubst → TransState → VerifM.Env → Prop),
    σ.wfIn Δ_base st.decls →
    (∀ p ∈ sargs, (p : TinyML.Typ × Term .value).2.wfIn st.decls) →
    VerifM.eval (Spec.declareArgs W.Θ σ args sargs) st ρ Ψ →
    ∃ σ' st' ρ', Ψ σ' st' ρ' ∧
      σ'.wfIn Δ_base st'.decls ∧
      st'.owns = st.owns ∧
      @TinyML.Typ.SubList W.Θ (sargs.map Prod.fst) (args.map Prod.snd) ∧
      ((Δ_base.declVars σ.dom).declVars (Spec.argVars args)).Subset
        (Δ_base.declVars σ'.dom) ∧
      VerifM.Env.agreeOn ((Δ_base.declVars σ.dom).declVars (Spec.argVars args))
        (VerifM.Env.withEnv ρ' (σ'.subst.eval ρ'.env))
        (Spec.argsEnv (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) args
          (sargs.map fun p => p.2.eval ρ.env)) := by
  intro args
  induction args with
  | nil =>
    intro sargs Δ_base σ st ρ Ψ hσwf _ heval
    cases sargs with
    | nil =>
      simp [Spec.declareArgs] at heval
      exact ⟨σ, st, ρ, VerifM.eval_ret heval, hσwf, rfl, .nil, Signature.Subset.refl _,
        by simp [Spec.argVars, Spec.argsEnv]; exact VerifM.Env.agreeOn_refl⟩
    | cons _ _ =>
      simp [Spec.declareArgs] at heval
      exact (VerifM.eval_fatal heval).elim
  | cons arg rest ih =>
    intro sargs Δ_base σ st ρ Ψ hσwf hsargs heval
    obtain ⟨name, ty⟩ := arg
    cases sargs with
    | nil =>
      simp [Spec.declareArgs] at heval
      exact (VerifM.eval_fatal heval).elim
    | cons sarg_hd sargs_rest =>
      obtain ⟨targ, sarg⟩ := sarg_hd
      simp only [Spec.declareArgs] at heval
      by_cases hsub_ty : TinyML.Typ.sub W.Θ targ ty = true
      · simp [hsub_ty] at heval
        have hdecl := VerifM.eval_decl
          (VerifM.eval_bind (VerifM.eval_ret (VerifM.eval_bind heval)))
        set argVar := st.freshConst (some name) .value
        set σ' := σ.rename ⟨name, .value⟩ argVar.name
        set ρ₁ := ρ.updateConst .value argVar.name (sarg.eval ρ.env)
        have hstwf : st.decls.wf := hσwf.useWf
        have hfresh_decls : argVar.name ∉ st.decls.allNames :=
          st.freshConst_fresh (some name) .value
        have hfresh_range : argVar.name ∉ σ.range.allNames :=
          hσwf.fresh_range hfresh_decls
        have hσ'wf : σ'.wfIn Δ_base (st.decls.addConst argVar) := by
          simpa [σ', argVar] using
            (FiniteSubst.rename_wfIn (σ := σ) (Δ_base := Δ_base) (Δ_use := st.decls)
              (v := ⟨name, .value⟩) (name' := argVar.name)
              hσwf hfresh_range hfresh_decls)
        have hsarg_wf : sarg.wfIn st.decls := hsargs _ (List.mem_cons_self ..)
        have hassume := VerifM.eval_assumePure
          (VerifM.eval_bind (hdecl (sarg.eval ρ.env)))
          (by
            simpa [argVar] using
              (Formula.eq_wfIn_addConst_of_fresh
                (Δ := st.decls) (c := argVar) hstwf hsarg_wf hfresh_decls))
          (by
            simpa [argVar, VerifM.Env.updateConst_env] using
              (Formula.eq_eval_updateConst_of_fresh
                (Δ := st.decls) (ρ := ρ.env) (c := argVar) hsarg_wf hfresh_decls))
        have hstwf_add : (st.decls.addConst argVar).wf := Signature.wf_addConst hstwf hfresh_decls
        have hsargs_rest : ∀ p ∈ sargs_rest, (p : TinyML.Typ × Term .value).2.wfIn
            (st.decls.addConst argVar) := fun p hp =>
          Term.wfIn_mono _ (hsargs p (List.mem_cons_of_mem _ hp))
            (Signature.Subset.subset_addConst _ _) hstwf_add
        have hsargs_eval : sargs_rest.map (fun p => p.2.eval ρ₁.env) =
            sargs_rest.map (fun p => p.2.eval ρ.env) :=
          List.map_congr_left fun p hp => Term.eval_env_agree
            (hsargs p (List.mem_cons_of_mem _ hp))
            (Env.agreeOn_symm (Env.agreeOn_update_fresh_const hfresh_decls))
        obtain ⟨σ'', st'', ρ'', hΨ, hσ''wf, howns, hsublist, hdom_sub, hagree⟩ :=
          ih sargs_rest Δ_base σ' _ ρ₁ Ψ hσ'wf hsargs_rest hassume
        refine ⟨σ'', st'', ρ'', hΨ, hσ''wf, howns,
          .cons (TinyML.Typ.sub_sound hsub_ty) hsublist, ?_, ?_⟩
        · change (((Δ_base.declVars σ.dom).declVar ⟨name, .value⟩).declVars
              (Spec.argVars rest)).Subset (Δ_base.declVars σ''.dom)
          simpa [σ', FiniteSubst.rename_source_eq] using hdom_sub
        · have hlen : rest.length ≤ sargs_rest.length := by
            have := TinyML.Typ.SubList.length_eq hsublist
            simp [List.length_map] at this; omega
          have hag_rename := FiniteSubst.rename_agreeOn
            (σ := σ) (Δ_base := Δ_base) (Δ_use := st.decls)
            (v := ⟨name, .value⟩) (name' := argVar.name)
            (ρ := ρ.env) (u := sarg.eval ρ.env) hσwf hfresh_range
          have hag_env := Spec.argsEnv_agreeOn
            (ρ₁ := VerifM.Env.withEnv ρ (σ'.subst.eval ρ₁.env))
            (ρ₂ := VerifM.Env.withEnv ρ ((σ.subst.eval ρ.env).updateConst .value name (sarg.eval ρ.env)))
            (by simpa [VerifM.Env.agreeOn, VerifM.Env.withEnv, σ', VerifM.Env.withEnv_env] using hag_rename)
            rest (sargs_rest.map fun p => p.2.eval ρ.env) (by simp [List.length_map]; omega)
          rw [hsargs_eval] at hagree
          change VerifM.Env.agreeOn
            (((Δ_base.declVars σ.dom).declVar ⟨name, .value⟩).declVars (Spec.argVars rest))
            (VerifM.Env.withEnv ρ'' (σ''.subst.eval ρ''.env))
            (Spec.argsEnv ((VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)).updateConst
              .value name (sarg.eval ρ.env)) rest
              (sargs_rest.map fun p => p.2.eval ρ.env))
          simpa [σ', FiniteSubst.rename_source_eq, Spec.argsEnv, VerifM.Env.withEnv,
            VerifM.Env.agreeOn] using
            (VerifM.Env.agreeOn_trans hagree hag_env)
      · simp [hsub_ty] at heval
        exact (VerifM.eval_fatal (VerifM.eval_bind heval)).elim

theorem call_correct (W : TinyML.World) (s : Spec) (Δ_base : Signature)
    (σ : FiniteSubst) (sargs : List (TinyML.Typ × Term .value))
    (st : TransState) (ρ : VerifM.Env)
    (Ψ : (TinyML.Typ × Term .value) → TransState → VerifM.Env → Prop)
    (Φ : Runtime.Val → iProp) (R : iProp) :
    s.pred.wfIn ((Δ_base.declVars σ.dom).declVars (Spec.argVars s.args)) →
    σ.wfIn Δ_base st.decls →
    (∀ p ∈ sargs, (p : TinyML.Typ × Term .value).2.wfIn st.decls) →
    VerifM.eval (Spec.call W.Θ σ s sargs) st ρ Ψ →
    (∀ v st' ρ' t, Ψ (s.retTy, t) st' ρ' → t.wfIn st'.decls → t.eval ρ'.env = v →
      st'.sl W ρ' ∗ R ∗ TinyML.ValHasType W v s.retTy ⊢ Φ v) →
    @TinyML.Typ.SubList W.Θ (sargs.map Prod.fst) (s.args.map Prod.snd) ∧
    (st.sl W ρ ∗ R ⊢ PredTrans.apply W (fun r => TinyML.ValHasType W r s.retTy -∗ Φ r) s.pred
      (Spec.argsEnv (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) s.args
        (sargs.map fun p => p.2.eval ρ.env))) := by
  intro hwf hσwf hsargs heval hΨ
  simp only [Spec.call] at heval
  have hb_grow := VerifM.eval.decls_grow ρ (VerifM.eval_bind heval)
  obtain ⟨σ', st', ρ', ⟨hdsub, hragree, hΨ'⟩, hσ'wf, howns, hsublist, hdom_sub, hagree⟩ :=
    declareArgs_correct W s.args sargs Δ_base σ st ρ _ hσwf hsargs hb_grow
  refine ⟨hsublist, ?_⟩
  have hwf'' : s.pred.wfIn (Δ_base.declVars σ'.dom) :=
    PredTrans.wfIn_mono hwf hdom_sub hσ'wf.srcWf
  have hcall := PredTrans.call_correct W s.pred Δ_base σ' st' ρ'
    _ (fun r => TinyML.ValHasType W r s.retTy -∗ Φ r) R
    hwf'' hσ'wf (VerifM.eval_bind hΨ')
    (fun v st'' ρ'' t hΨ'' htwf hteval => by
      apply wand_intro
      iintro ⟨⟨Howns, HR⟩, Hty⟩
      iintuitionistic Hty
      ihave Hpure := (TinyML.typeConstraints_hold (ty := s.retTy) (t := t) (ρ := ρ''.env) (W := W) (v := v) hteval) $$ Hty
      ipure Hpure
      obtain ⟨st₃, hst₃_decls, hst₃_owns, _, hret⟩ :=
        VerifM.eval_assumeAll (VerifM.eval_bind hΨ'')
          (fun φ hφ => TinyML.typeConstraints_wfIn htwf φ hφ)
          (fun φ hφ => Hpure φ hφ)
      ihave Harg : (st₃.sl W ρ'' ∗ R ∗ TinyML.ValHasType W v s.retTy) $$ [HR Howns Hty]
      · iframe HR Hty
        simp [TransState.sl, hst₃_owns]; iassumption
      iapply (hΨ v st₃ ρ'' t (VerifM.eval_ret hret) (hst₃_decls ▸ htwf) hteval) $$ Harg)
  exact (sep_mono_left (SpatialContext.interp_env_agree W (VerifM.eval.wf heval).ownsWf hragree).1).trans <|
    (by simpa [howns] using hcall : st.sl W ρ' ∗ R ⊢ _).trans <|
    PredTrans.apply_env_agree W hwf hagree

end CallCorrectness

/-! ## Implementation Protocol Correctness -/
section ImplementCorrectness

/-- Correctness payload for `declareImplArgs`. -/
def DeclareImplArgs.Result (args : List (String × TinyML.Typ)) (vs : List Runtime.Val)
    (Δ_base : Signature) (σ : FiniteSubst) (st : TransState) (ρ : VerifM.Env)
    (Ψ : (FiniteSubst × List FOL.Const) → TransState → VerifM.Env → Prop) : Prop :=
  ∃ σ' implVars st' ρ', Ψ (σ', implVars) st' ρ' ∧
    σ'.wfIn Δ_base st'.decls ∧
    st.decls.Subset st'.decls ∧
    VerifM.Env.agreeOn st.decls ρ ρ' ∧
    st'.owns = st.owns ∧
    ((Δ_base.declVars σ.dom).declVars (argVars args)).Subset
      (Δ_base.declVars σ'.dom) ∧
    VerifM.Env.agreeOn ((Δ_base.declVars σ.dom).declVars (argVars args))
      (VerifM.Env.withEnv ρ' (σ'.subst.eval ρ'.env))
      (argsEnv (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) args vs) ∧
    (∀ v ∈ implVars, v ∈ st'.decls.consts) ∧
    (∀ v ∈ implVars, v.sort = .value) ∧
    Terms.Eval ρ'.env (implVars.map (fun av => .const (.uninterpreted av.name .value))) vs

theorem declareImplArgs_correct (W : TinyML.World) :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val)
      (Δ_base : Signature) (σ : FiniteSubst) (st : TransState) (ρ : VerifM.Env)
      (Ψ : (FiniteSubst × List FOL.Const) → TransState → VerifM.Env → Prop),
    σ.wfIn Δ_base st.decls →
    VerifM.eval (Spec.declareImplArgs σ args) st ρ Ψ →
    TinyML.ValsHaveTypes W vs (args.map Prod.snd) ⊢
      ⌜Spec.DeclareImplArgs.Result args vs Δ_base σ st ρ Ψ⌝ := by
  intro args
  induction args with
  | nil =>
    intro vs Δ_base σ st ρ Ψ hσwf heval
    iintro Hvs
    ihave %hlen := TinyML.ValsHaveTypes.length_eq $$ Hvs
    cases vs with
    | nil =>
      simp [Spec.declareImplArgs] at heval
      have := VerifM.eval_ret heval
      ipureintro
      exact ⟨σ, [], st, ρ, this, hσwf,
        Signature.Subset.refl _, VerifM.Env.agreeOn_refl, rfl, Signature.Subset.refl _,
        by simp [Spec.argVars, Spec.argsEnv]; exact VerifM.Env.agreeOn_refl,
        nofun,
        nofun,
        .nil⟩
    | cons _ _ =>
      simp at hlen
  | cons arg rest ih =>
    intro vs Δ_base σ st ρ Ψ hσwf heval
    obtain ⟨name, ty⟩ := arg
    cases vs with
    | nil =>
      exact (TinyML.ValsHaveTypes.nil_cons W ty (rest.map Prod.snd)).1.trans false_elim
    | cons v vs' =>
      refine (TinyML.ValsHaveTypes.cons W v vs' ty (rest.map Prod.snd)).1.trans ?_
      iintro Hvs
      icases Hvs with ⟨Hv, Hvs_rest⟩
      simp only [Spec.declareImplArgs] at heval
      have hdecl := VerifM.eval_decl (VerifM.eval_bind heval)
      set argVar := st.freshConst (some name) .value
      set σ' := σ.rename ⟨name, .value⟩ argVar.name
      set ρ₁ := ρ.updateConst .value argVar.name v
      specialize hdecl v
      have hstwf : st.decls.wf := hσwf.useWf
      have hfresh_decls : argVar.name ∉ st.decls.allNames :=
        st.freshConst_fresh (some name) .value
      have hfresh_range : argVar.name ∉ σ.range.allNames :=
        hσwf.fresh_range hfresh_decls
      have hσ'wf : σ'.wfIn Δ_base (st.decls.addConst argVar) := by
        simpa [σ', argVar] using
          (FiniteSubst.rename_wfIn (σ := σ) (Δ_base := Δ_base) (Δ_use := st.decls)
            (v := ⟨name, .value⟩) (name' := argVar.name)
            hσwf hfresh_range hfresh_decls)
      have hvar_wf : (Term.const (.uninterpreted argVar.name .value)).wfIn (st.decls.addConst argVar) := by
        simpa using
          (Term.const_wfIn_addConst_of_fresh (Δ := st.decls) (c := argVar) hstwf hfresh_decls)
      have hvar_eval : (Term.const (.uninterpreted argVar.name .value)).eval ρ₁.env = v := by
        simp [ρ₁]
      ihave %htyped_formulas := TinyML.typeConstraints_hold (ty := ty)
          (t := .const (.uninterpreted argVar.name .value))
          (ρ := ρ₁.env) (W := W) (v := v) hvar_eval $$ Hv
      obtain ⟨st₂, hst₂_decls, hst₂_owns, _, hdecl₂⟩ :=
        VerifM.eval_assumeAll (VerifM.eval_bind hdecl)
          (fun φ hφ => TinyML.typeConstraints_wfIn hvar_wf φ hφ)
          (fun φ hφ => htyped_formulas φ hφ)
      have hst_st₂ : st.decls.Subset st₂.decls :=
        hst₂_decls ▸ Signature.Subset.subset_addConst _ _
      ihave %hih := ih vs' Δ_base σ' st₂ ρ₁
        (fun p st' ρ' => Ψ (p.1, argVar :: p.2) st' ρ')
        (hst₂_decls ▸ hσ'wf)
        ((VerifM.eval_bind hdecl₂).mono (fun _ _ _ hp => VerifM.eval_ret hp))
        $$ Hvs_rest
      obtain ⟨σ'', argVars', st', ρ', hΨ, hσ''wf, hdsub', hragree',
        howns, hdom_sub, hagree, hmem_decls, hsorts, hlookups⟩ := hih
      ihave %hlen_rest := TinyML.ValsHaveTypes.length_eq $$ Hvs_rest
      have hag_rename := FiniteSubst.rename_agreeOn
        (σ := σ) (Δ_base := Δ_base) (Δ_use := st.decls)
        (v := ⟨name, .value⟩) (name' := argVar.name)
        (ρ := ρ.env) (u := v) hσwf hfresh_range
      have hag_env := Spec.argsEnv_agreeOn
        (ρ₁ := VerifM.Env.withEnv ρ₁ (σ'.subst.eval ρ₁.env))
        (ρ₂ := VerifM.Env.withEnv ρ ((σ.subst.eval ρ.env).updateConst .value name v))
        (by simpa [VerifM.Env.agreeOn, VerifM.Env.withEnv, σ', VerifM.Env.withEnv_env] using hag_rename)
        rest vs' (by simp [List.length_map] at hlen_rest; omega)
      ipureintro
      refine ⟨σ'', argVar :: argVars', st', ρ', hΨ, hσ''wf,
        Signature.Subset.trans hst_st₂ hdsub',
        VerifM.Env.agreeOn_trans
          (VerifM.Env.agreeOn_update_fresh (ρ := ρ) (c := argVar) (u := v) hfresh_decls)
          (VerifM.Env.agreeOn_mono hst_st₂ hragree'),
        howns.trans hst₂_owns, ?_, ?_, ?_, ?_, ?_⟩
      · change (((Δ_base.declVars σ.dom).declVar ⟨name, .value⟩).declVars
            (Spec.argVars rest)).Subset (Δ_base.declVars σ''.dom)
        simpa [σ', FiniteSubst.rename_source_eq] using hdom_sub
      · change VerifM.Env.agreeOn
          (((Δ_base.declVars σ.dom).declVar ⟨name, .value⟩).declVars (Spec.argVars rest))
          (VerifM.Env.withEnv ρ' (σ''.subst.eval ρ'.env))
          (Spec.argsEnv ((VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)).updateConst .value name v)
            rest vs')
        simpa [σ', FiniteSubst.rename_source_eq, Spec.argsEnv, VerifM.Env.withEnv,
          VerifM.Env.agreeOn] using
          (VerifM.Env.agreeOn_trans hagree hag_env)
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
        have h1' : Term.eval ρ'.env (Term.const (.uninterpreted argVar.name .value)) =
            Term.eval ρ₁.env (Term.const (.uninterpreted argVar.name .value)) := by
          simpa [Term.eval, Const.denote, Env.lookupConst] using h1.symm
        exact h1'.trans hvar_eval

theorem implement_correct (W : TinyML.World) (s : Spec) (body : List FOL.Const → VerifM (Term .value))
    (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (st : TransState) (ρ : VerifM.Env) (vs : List Runtime.Val) (Φ : Runtime.Val → iProp) (R : iProp) :
    s.wfIn Δ_spec →
    Δ_spec.Subset st.decls →
    VerifM.Env.agreeOn Δ_spec ρ_spec ρ →
    Δ_spec.wf →
    Δ_spec.vars = [] →
    VerifM.eval (Spec.implement Δ_spec s body) st ρ (fun _ _ _ => True) →
    (∀ (argVars : List FOL.Const) (st' : TransState) (ρ' : VerifM.Env) (Q : iProp),
      st.decls.Subset st'.decls →
      VerifM.Env.agreeOn st.decls ρ ρ' →
      (∀ v ∈ argVars, v ∈ st'.decls.consts) →
      (∀ v ∈ argVars, v.sort = .value) →
      List.Forall₂ (fun av val => ρ'.env.consts .value av.name = val) argVars vs →
      VerifM.eval (body argVars) st' ρ'
        (fun result st'' ρ'' =>
          ∀ (S : iProp), result.wfIn st''.decls →
            st''.sl W ρ'' ∗ Q ∗ ((TinyML.ValHasType W (result.eval ρ''.env) s.retTy -∗ Φ (result.eval ρ''.env)) -∗ S) ⊢ S) →
      st'.sl W ρ' ∗ Q ⊢ R) →
    st.sl W ρ ∗ TinyML.ValsHaveTypes W vs (s.args.map Prod.snd) ∗
      PredTrans.apply W (fun r => TinyML.ValHasType W r s.retTy -∗ Φ r) s.pred
        (Spec.argsEnv ρ_spec s.args vs) ⊢ R := by
  intro hswf hΔspec hρspec hΔwf hΔvars heval hbody
  simp only [Spec.implement] at heval
  have hb := VerifM.eval_bind heval
  iintro H
  icases H with ⟨Howns, Hvals, Happ⟩
  iintuitionistic Hvals
  ihave %hlen_vals := TinyML.ValsHaveTypes.length_eq $$ Hvals
  ihave Hdecl := declareImplArgs_correct W s.args vs Δ_spec (FiniteSubst.base Δ_spec) st ρ _
      (FiniteSubst.base_wfIn hΔspec hΔwf (VerifM.eval.wf heval).namesDisjoint hΔvars)
      hb $$ Hvals
  ipure Hdecl
  obtain ⟨σ', argVars, st', ρ', hΨ, hσ'wf, hdsub, hragree, howns, hdom_sub, hagree,
    hmem_decls, hsorts, hlookups⟩ := Hdecl
  have hag_base :
      VerifM.Env.agreeOn (Δ_spec.declVars (Spec.argVars s.args))
        (Spec.argsEnv ρ_spec s.args vs)
            (Spec.argsEnv (VerifM.Env.withEnv ρ ((FiniteSubst.base Δ_spec).subst.eval ρ.env)) s.args vs) :=
    Spec.argsEnv_agreeOn (Δ := Δ_spec)
      (ρ₁ := ρ_spec)
      (ρ₂ := VerifM.Env.withEnv ρ ((FiniteSubst.base Δ_spec).subst.eval ρ.env))
      (by simpa [FiniteSubst.base, VerifM.Env.withEnv] using hρspec)
      s.args vs
      (by
        simp [List.length_map] at hlen_vals
        omega)
  have hst'_wf : st'.decls.wf := (VerifM.eval.wf hΨ).namesDisjoint
  iapply (show st'.sl W ρ' ∗
        PredTrans.apply W (fun r => TinyML.ValHasType W r s.retTy -∗ Φ r) s.pred
          (VerifM.Env.withEnv ρ' (σ'.subst.eval ρ'.env)) ⊢ R from
    PredTrans.implement_correct W s.pred Δ_spec σ' (body argVars) st' ρ'
      (fun r => TinyML.ValHasType W r s.retTy -∗ Φ r) R
      (PredTrans.wfIn_mono hswf hdom_sub hσ'wf.srcWf)
      hσ'wf hΨ
      (fun st'' ρ'' Q hdsub' hragree' hbody_eval => by
        apply hbody argVars st'' ρ'' Q
          (hdsub.trans hdsub')
          (VerifM.Env.agreeOn_trans hragree (VerifM.Env.agreeOn_mono hdsub hragree'))
          (fun v hv => hdsub'.consts v (hmem_decls v hv)) hsorts
        · refine Terms.Eval.lookup_const (Terms.Eval.env_agree (ρ := ρ'.env) ?_ hragree' hlookups)
          intro t ht
          obtain ⟨av, hav, rfl⟩ := List.mem_map.mp ht
          obtain ⟨_, _⟩ := av
          have hsort := hsorts _ hav
          cases hsort
          exact Term.const_wfIn_of_mem hst'_wf (hmem_decls _ hav)
        · exact hbody_eval))
  isplitr [Happ]
  · iapply (show st.sl W ρ' ⊢ st'.sl W ρ' by simp [howns, TransState.sl])
    iapply (show st.sl W ρ ⊢ st.sl W ρ' by
      simpa [TransState.sl] using
        (SpatialContext.interp_env_agree W (VerifM.eval.wf heval).ownsWf hragree).1)
    iexact Howns
  · iapply (PredTrans.apply_env_agree W hswf (VerifM.Env.agreeOn_trans hag_base (by
        simpa [FiniteSubst.base, Signature.declVars] using VerifM.Env.agreeOn_symm hagree)))
    iexact Happ

end ImplementCorrectness
end Spec

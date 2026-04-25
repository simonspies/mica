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

/-!
# Specifications

Defines `Spec`, `SpecMap`, and related operations built on top of `PredTrans`.
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

namespace Spec

/-! ## Definitions -/

/-- The list of SMT variables corresponding to a spec's arguments. -/
def argVars (args : List (String × TinyML.Typ)) : List Var :=
  args.map fun (name, _) => ⟨name, .value⟩

/-- Build an environment binding each argument name to its value, left-to-right.
    Later arguments shadow earlier ones with the same name. -/
def argsEnv (ρ : VerifM.Env) : List (String × TinyML.Typ) → List Runtime.Val → VerifM.Env
  | [], _ | _, [] => ρ
  | (name, _) :: rest, v :: vs => argsEnv (ρ.updateConst .value name v) rest vs

def isPrecondFor (Θ : TinyML.TypeEnv) (f : Runtime.Val) (s : Spec) : iProp :=
  iprop(□ ∀ (Φ : Runtime.Val → iProp) (vs : List Runtime.Val),
      TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd) -∗
        PredTrans.apply (fun r => TinyML.ValHasType Θ r s.retTy -∗ Φ r) s.pred
          (argsEnv VerifM.Env.empty s.args vs) -∗
        wp (Runtime.Expr.app (.val f) (vs.map fun v => .val v)) Φ)

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
  VerifM.assumeAll (typeConstraints s.retTy result)
  pure (s.retTy, result)

/-- Declare implementation argument variables: for each `(name, ty)` in `args`,
    declare a fresh variable, assume its type constraints, and rename in `σ`.
    Returns the final substitution and the list of declared argument variables. -/
def declareImplArgs (σ : FiniteSubst) :
    List (String × TinyML.Typ) → VerifM (FiniteSubst × List FOL.Const)
  | [] => pure (σ, [])
  | (name, ty) :: rest => do
    let argVar ← VerifM.decl (some name) .value
    VerifM.assumeAll (typeConstraints ty (.const (.uninterpreted argVar.name .value)))
    let σ' := σ.rename ⟨name, .value⟩ argVar.name
    let (σ'', vars) ← declareImplArgs σ' rest
    pure (σ'', argVar :: vars)

/-- Full implementation protocol for a spec: declare argument variables,
    assume type constraints, then invoke `PredTrans.implement`. Dual to `call`. -/
def implement (s : Spec) (body : List FOL.Const → VerifM (Term .value)) : VerifM Unit := do
  let (σ, argVars) ← declareImplArgs FiniteSubst.id s.args
  PredTrans.implement σ s.pred (body argVars)

/-! ## Precondition Proofs -/
section Precondition

instance : Iris.BI.Persistent (isPrecondFor Θ f s) := by
  unfold isPrecondFor
  infer_instance

/-- Fold `wp_fix'`'s tupled recursive obligation into a spec precondition;
    the two differ only by currying the typing hypothesis and the predicate transformer. -/
theorem isPrecondFor_fold (Θ : TinyML.TypeEnv) (s : Spec)
    (f : Runtime.Val) :
    iprop(□ ∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
      (TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd) ∗
        PredTrans.apply (fun r => TinyML.ValHasType Θ r s.retTy -∗ P r) s.pred
          (argsEnv VerifM.Env.empty s.args vs)) -∗
        wp (Runtime.Expr.app (.val f) (vs.map Runtime.Expr.val)) P) ⊢ s.isPrecondFor Θ f := by
  unfold isPrecondFor
  iintro □H
  imodintro
  iintro %Φ %vs Htyped Hpred
  ispecialize H $$ %vs %Φ
  iapply H
  isplitl [Htyped]
  · iexact Htyped
  · iexact Hpred

/-- Löb-style rule for spec preconditions on `fix`: to prove
    `s.isPrecondFor Θ (.fix f args e)`, assume it as the recursive hypothesis and
    prove the `wp` of the body (after the usual fix-substitution). -/
theorem isPrecondFor_fix {Θ : TinyML.TypeEnv} {s : Spec}
    {f : Runtime.Binder} {args : List Runtime.Binder} {e : Runtime.Expr}
    {R : iProp}
    (h : R ⊢ □ (s.isPrecondFor Θ (.fix f args e) -∗
        ∀ (vs : List Runtime.Val) (P : Runtime.Val → iProp),
          TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd) -∗
          PredTrans.apply (fun r => TinyML.ValHasType Θ r s.retTy -∗ P r) s.pred
              (argsEnv VerifM.Env.empty s.args vs) -∗
          wp (e.subst ((Runtime.Subst.id.update' f (.fix f args e)).updateAll' args vs)) P)) :
    R ⊢ s.isPrecondFor Θ (.fix f args e) := by
  refine (SpatialContext.wp_fix' (Φ := fun P vs =>
      iprop(TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd) ∗
        PredTrans.apply (fun r => TinyML.ValHasType Θ r s.retTy -∗ P r) s.pred
            (argsEnv VerifM.Env.empty s.args vs))) (h.trans ?_)).trans
    (isPrecondFor_fold Θ s _)
  istart
  iintro □HR
  imodintro
  iintro IH %vs %P ⟨htyped, hpred⟩
  ispecialize HR $$ [IH]
  · iapply (isPrecondFor_fold Θ s (.fix f args e))
    iexact IH
  ihave Hres := HR $$ %vs %P [htyped] [hpred]
  · iexact htyped
  · iexact hpred
  iexact Hres

end Precondition

/-! ## Well-Formedness Proofs -/
section WellFormedness

theorem checkWf_ok {spec : Spec} {Δ : Signature}
    (h : spec.checkWf Δ = .ok ()) : spec.wfIn Δ :=
  PredTrans.checkWf_ok h

theorem wfIn_mono {spec : Spec} {Δ Δ' : Signature}
    (h : spec.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) :
    spec.wfIn Δ' :=
  PredTrans.wfIn_mono h (Signature.Subset.declVars hsub (argVars spec.args))
    (Signature.wf_declVars hwf)

end WellFormedness

/-! ## Environment Agreement -/
section EnvironmentAgreement

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

/-- Correctness of `declareArgs`: after processing all arguments, the resulting
    substitution is well-formed, types match, and the env agrees with `argsEnv`. -/
theorem declareArgs_correct (Θ : TinyML.TypeEnv) :
    ∀ (args : List (String × TinyML.Typ)) (sargs : List (TinyML.Typ × Term .value))
      (σ : FiniteSubst) (st : TransState) (ρ : VerifM.Env)
      (Ψ : FiniteSubst → TransState → VerifM.Env → Prop),
    σ.wf st.decls →
    (Signature.ofVars σ.dom).wf →
    (∀ p ∈ sargs, (p : TinyML.Typ × Term .value).2.wfIn st.decls) →
    VerifM.eval (Spec.declareArgs Θ σ args sargs) st ρ Ψ →
    ∃ σ' st' ρ', Ψ σ' st' ρ' ∧
      σ'.wf st'.decls ∧
      (Signature.ofVars σ'.dom).wf ∧
      st'.owns = st.owns ∧
      @TinyML.Typ.SubList Θ (sargs.map Prod.fst) (args.map Prod.snd) ∧
      (((Signature.ofVars σ.dom).declVars (Spec.argVars args)).vars ⊆ σ'.dom) ∧
      VerifM.Env.agreeOn ((Signature.ofVars σ.dom).declVars (Spec.argVars args))
        (VerifM.Env.withEnv ρ' (σ'.subst.eval ρ'.env))
        (Spec.argsEnv (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) args
          (sargs.map fun p => p.2.eval ρ.env)) := by
  intro args
  induction args with
  | nil =>
    intro sargs σ st ρ Ψ hσwf hσdomwf _ heval
    cases sargs with
    | nil =>
      simp [Spec.declareArgs] at heval
      exact ⟨σ, st, ρ, VerifM.eval_ret heval, hσwf, hσdomwf, rfl, .nil, fun _ hx => hx,
        by simp [Spec.argVars, Spec.argsEnv]; exact VerifM.Env.agreeOn_refl⟩
    | cons _ _ =>
      simp [Spec.declareArgs] at heval
      exact (VerifM.eval_fatal heval).elim
  | cons arg rest ih =>
    intro sargs σ st ρ Ψ hσwf hσdomwf hsargs heval
    obtain ⟨name, ty⟩ := arg
    cases sargs with
    | nil =>
      simp [Spec.declareArgs] at heval
      exact (VerifM.eval_fatal heval).elim
    | cons sarg_hd sargs_rest =>
      obtain ⟨targ, sarg⟩ := sarg_hd
      simp only [Spec.declareArgs] at heval
      by_cases hsub_ty : TinyML.Typ.sub Θ targ ty = true
      · simp [hsub_ty] at heval
        have hdecl := VerifM.eval_decl
          (VerifM.eval_bind _ _ _ _ (VerifM.eval_ret (VerifM.eval_bind _ _ _ _ heval)))
        set argVar := st.freshConst (some name) .value
        set σ' := σ.rename ⟨name, .value⟩ argVar.name
        set ρ₁ := ρ.updateConst .value argVar.name (sarg.eval ρ.env)
        have hstwf : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
        obtain ⟨hfresh_decls, _hfresh_range, hσ'wf, hσ'domwf⟩ :=
          FiniteSubst.rename_bundle_of_freshConst (hint := some name) (v := ⟨name, .value⟩) hσwf hσdomwf
        have hsarg_wf : sarg.wfIn st.decls := hsargs _ (List.mem_cons_self ..)
        have hassume := VerifM.eval_assumePure
          (VerifM.eval_bind _ _ _ _ (hdecl (sarg.eval ρ.env)))
          (TransState.freshConst_eq_wfIn hstwf hsarg_wf hfresh_decls)
          (TransState.freshConst_eq_eval (ρ := ρ) hsarg_wf hfresh_decls)
        have hstwf_add : (st.decls.addConst argVar).wf := Signature.wf_addConst hstwf hfresh_decls
        have hsargs_rest : ∀ p ∈ sargs_rest, (p : TinyML.Typ × Term .value).2.wfIn
            (st.decls.addConst argVar) := fun p hp =>
          Term.wfIn_mono _ (hsargs p (List.mem_cons_of_mem _ hp))
            (Signature.Subset.subset_addConst _ _) hstwf_add
        have hsargs_eval : sargs_rest.map (fun p => p.2.eval ρ₁.env) =
            sargs_rest.map (fun p => p.2.eval ρ.env) :=
          List.map_congr_left fun p hp => Term.eval_env_agree
            (hsargs p (List.mem_cons_of_mem _ hp))
            (Env.agreeOn_symm (agreeOn_update_fresh_const hfresh_decls))
        obtain ⟨σ'', st'', ρ'', hΨ, hσ''wf, hσ''domwf, howns, hsublist, hdom_sub, hagree⟩ :=
          ih sargs_rest σ' _ ρ₁ Ψ hσ'wf hσ'domwf hsargs_rest hassume
        refine ⟨σ'', st'', ρ'', hΨ, hσ''wf, hσ''domwf, howns,
          .cons (TinyML.Typ.sub_sound hsub_ty) hsublist, ?_, ?_⟩
        · simpa [σ', FiniteSubst.rename, Signature.ofVars, Spec.argVars,
                 Signature.declVars, Signature.declVar] using hdom_sub
        · have hlen : rest.length ≤ sargs_rest.length := by
            have := TinyML.Typ.SubList.length_eq hsublist
            simp [List.length_map] at this; omega
          have hag_rename := FiniteSubst.rename_agreeOn_declVar
            (σ := σ) (decls := st.decls) (v := ⟨name, .value⟩) (c := argVar)
            (ρ := ρ.env) (u := sarg.eval ρ.env) hσwf hfresh_decls rfl
          have hag_env := Spec.argsEnv_agreeOn
            (ρ₁ := VerifM.Env.withEnv ρ (σ'.subst.eval ρ₁.env))
            (ρ₂ := VerifM.Env.withEnv ρ ((σ.subst.eval ρ.env).updateConst .value name (sarg.eval ρ.env)))
            (by simpa [VerifM.Env.agreeOn, VerifM.Env.withEnv, σ', FiniteSubst.rename] using hag_rename)
            rest (sargs_rest.map fun p => p.2.eval ρ.env) (by simp [List.length_map]; omega)
          rw [hsargs_eval] at hagree
          simpa [σ', FiniteSubst.rename, Spec.argsEnv, Spec.argVars, Signature.declVars,
            Signature.declVar, VerifM.Env.withEnv, VerifM.Env.agreeOn] using
            (VerifM.Env.agreeOn_trans hagree hag_env)
      · simp [hsub_ty] at heval
        exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ heval)).elim

theorem call_correct (Θ : TinyML.TypeEnv) (s : Spec) (σ : FiniteSubst) (sargs : List (TinyML.Typ × Term .value))
    (st : TransState) (ρ : VerifM.Env)
    (Ψ : (TinyML.Typ × Term .value) → TransState → VerifM.Env → Prop)
    (Φ : Runtime.Val → iProp) (R : iProp) :
    s.pred.wfIn ((Signature.ofVars σ.dom).declVars (Spec.argVars s.args)) →
    (Signature.ofVars σ.dom).wf →
    σ.wf st.decls →
    (∀ p ∈ sargs, (p : TinyML.Typ × Term .value).2.wfIn st.decls) →
    VerifM.eval (Spec.call Θ σ s sargs) st ρ Ψ →
    (∀ v st' ρ' t, Ψ (s.retTy, t) st' ρ' → t.wfIn st'.decls → t.eval ρ'.env = v →
      st'.sl ρ' ∗ R ∗ TinyML.ValHasType Θ v s.retTy ⊢ Φ v) →
    @TinyML.Typ.SubList Θ (sargs.map Prod.fst) (s.args.map Prod.snd) ∧
    (st.sl ρ ∗ R ⊢ PredTrans.apply (fun r => TinyML.ValHasType Θ r s.retTy -∗ Φ r) s.pred
      (Spec.argsEnv (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) s.args
        (sargs.map fun p => p.2.eval ρ.env))) := by
  intro hwf hσdomwf hσwf hsargs heval hΨ
  simp only [Spec.call] at heval
  have hb_grow := VerifM.eval.decls_grow ρ (VerifM.eval_bind _ _ _ _ heval)
  obtain ⟨σ', st', ρ', ⟨hdsub, hragree, hΨ'⟩, hσ'wf, hσ'domwf, howns, hsublist, hdom_sub, hagree⟩ :=
    declareArgs_correct Θ s.args sargs σ st ρ _ hσwf hσdomwf hsargs hb_grow
  refine ⟨hsublist, ?_⟩
  have hwf'' : s.pred.wfIn (Signature.ofVars σ'.dom) :=
    PredTrans.wfIn_mono hwf (Signature.Subset.ofVars hdom_sub) hσ'domwf
  have hcall := PredTrans.call_correct s.pred σ' st' ρ'
    _ (fun r => TinyML.ValHasType Θ r s.retTy -∗ Φ r) R
    hwf'' hσ'domwf hσ'wf (VerifM.eval_bind _ _ _ _ hΨ')
    (fun v st'' ρ'' t hΨ'' htwf hteval => by
      apply wand_intro
      iintro H
      icases H with ⟨⟨Howns, HR⟩, Hty⟩
      iintuitionistic Hty
      ihave Hpure := (typeConstraints_hold (ty := s.retTy) (t := t) (ρ := ρ''.env) (Θ := Θ) (v := v) hteval) $$ Hty
      ipure Hpure
      obtain ⟨st₃, hst₃_decls, hst₃_owns, hret⟩ :=
        VerifM.eval_assumeAll (VerifM.eval_bind _ _ _ _ hΨ'')
          (fun φ hφ => typeConstraints_wfIn htwf φ hφ)
          (fun φ hφ => Hpure φ hφ)
      ihave Harg : (st₃.sl ρ'' ∗ R ∗ TinyML.ValHasType Θ v s.retTy) $$ [HR Howns Hty]
      · isplitr [Hty HR]
        · simp [TransState.sl, hst₃_owns]; iassumption
        · isplitl [HR]
          · iexact HR
          · iexact Hty
      iapply (hΨ v st₃ ρ'' t (VerifM.eval_ret hret) (hst₃_decls ▸ htwf) hteval) $$ Harg)
  exact (sep_mono_l (SpatialContext.interp_env_agree (VerifM.eval.wf heval).ownsWf hragree).1).trans <|
    (by simpa [howns] using hcall : st.sl ρ' ∗ R ⊢ _).trans <|
    PredTrans.apply_env_agree hwf hagree

end CallCorrectness

/-! ## Implementation Protocol Correctness -/
section ImplementCorrectness

/-- Correctness payload for `declareImplArgs`. -/
def DeclareImplArgs.Result (args : List (String × TinyML.Typ)) (vs : List Runtime.Val)
    (σ : FiniteSubst) (st : TransState) (ρ : VerifM.Env)
    (Ψ : (FiniteSubst × List FOL.Const) → TransState → VerifM.Env → Prop) : Prop :=
  ∃ σ' implVars st' ρ', Ψ (σ', implVars) st' ρ' ∧
    σ'.wf st'.decls ∧
    (Signature.ofVars σ'.dom).wf ∧
    st.decls.Subset st'.decls ∧
    VerifM.Env.agreeOn st.decls ρ ρ' ∧
    st'.owns = st.owns ∧
    (((Signature.ofVars σ.dom).declVars (argVars args)).vars ⊆ σ'.dom) ∧
    VerifM.Env.agreeOn ((Signature.ofVars σ.dom).declVars (argVars args))
      (VerifM.Env.withEnv ρ' (σ'.subst.eval ρ'.env))
      (argsEnv (VerifM.Env.withEnv ρ (σ.subst.eval ρ.env)) args vs) ∧
    (∀ v ∈ implVars, v ∈ st'.decls.consts) ∧
    (∀ v ∈ implVars, v.sort = .value) ∧
    Terms.Eval ρ'.env (implVars.map (fun av => .const (.uninterpreted av.name .value))) vs

theorem declareImplArgs_correct (Θ : TinyML.TypeEnv) :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val)
      (σ : FiniteSubst) (st : TransState) (ρ : VerifM.Env)
      (Ψ : (FiniteSubst × List FOL.Const) → TransState → VerifM.Env → Prop),
    σ.wf st.decls →
    (Signature.ofVars σ.dom).wf →
    VerifM.eval (Spec.declareImplArgs σ args) st ρ Ψ →
    TinyML.ValsHaveTypes Θ vs (args.map Prod.snd) ⊢
      ⌜Spec.DeclareImplArgs.Result args vs σ st ρ Ψ⌝ := by
  intro args
  induction args with
  | nil =>
    intro vs σ st ρ Ψ hσwf hσdomwf heval
    iintro Hvs
    ihave %hlen := TinyML.ValsHaveTypes.length_eq $$ Hvs
    cases vs with
    | nil =>
      simp [Spec.declareImplArgs] at heval
      have := VerifM.eval_ret heval
      ipure_intro
      exact ⟨σ, [], st, ρ, this, hσwf, hσdomwf,
        Signature.Subset.refl _, VerifM.Env.agreeOn_refl, rfl, fun x hx => hx,
        by simp [Spec.argVars, Spec.argsEnv]; exact VerifM.Env.agreeOn_refl,
        nofun,
        nofun,
        .nil⟩
    | cons _ _ =>
      simp at hlen
  | cons arg rest ih =>
    intro vs σ st ρ Ψ hσwf hσdomwf heval
    obtain ⟨name, ty⟩ := arg
    cases vs with
    | nil =>
      exact (TinyML.ValsHaveTypes.nil_cons Θ ty (rest.map Prod.snd)).1.trans false_elim
    | cons v vs' =>
      refine (TinyML.ValsHaveTypes.cons Θ v vs' ty (rest.map Prod.snd)).1.trans ?_
      iintro Hvs
      icases Hvs with ⟨Hv, Hvs_rest⟩
      simp only [Spec.declareImplArgs] at heval
      have hdecl := VerifM.eval_decl (VerifM.eval_bind _ _ _ _ heval)
      set argVar := st.freshConst (some name) .value
      set σ' := σ.rename ⟨name, .value⟩ argVar.name
      set ρ₁ := ρ.updateConst .value argVar.name v
      specialize hdecl v
      have hstwf : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
      obtain ⟨hfresh_decls, _hfresh_range, hσ'wf, hσ'domwf⟩ :=
        FiniteSubst.rename_bundle_of_freshConst (hint := some name) (v := ⟨name, .value⟩) hσwf hσdomwf
      have hvar_wf := TransState.freshConst_wfIn (hint := some name) hstwf hfresh_decls
      have hvar_eval : (Term.const (.uninterpreted argVar.name .value)).eval ρ₁.env = v := by
        simp [ρ₁]
      ihave %htyped_formulas := typeConstraints_hold (ty := ty)
          (t := .const (.uninterpreted argVar.name .value))
          (ρ := ρ₁.env) (Θ := Θ) (v := v) hvar_eval $$ Hv
      obtain ⟨st₂, hst₂_decls, hst₂_owns, hdecl₂⟩ :=
        VerifM.eval_assumeAll (VerifM.eval_bind _ _ _ _ hdecl)
          (fun φ hφ => typeConstraints_wfIn hvar_wf φ hφ)
          (fun φ hφ => htyped_formulas φ hφ)
      have hst_st₂ : st.decls.Subset st₂.decls :=
        hst₂_decls ▸ Signature.Subset.subset_addConst _ _
      ihave %hih := ih vs' σ' st₂ ρ₁
        (fun p st' ρ' => Ψ (p.1, argVar :: p.2) st' ρ')
        (hst₂_decls ▸ hσ'wf) hσ'domwf
        ((VerifM.eval_bind _ _ _ _ hdecl₂).mono (fun _ _ _ hp => VerifM.eval_ret hp))
        $$ Hvs_rest
      obtain ⟨σ'', argVars', st', ρ', hΨ, hσ''wf, hσ''domwf, hdsub', hragree',
        howns, hdom_sub, hagree, hmem_decls, hsorts, hlookups⟩ := hih
      ihave %hlen_rest := TinyML.ValsHaveTypes.length_eq $$ Hvs_rest
      have hag_rename := FiniteSubst.rename_agreeOn_declVar
        (σ := σ) (decls := st.decls) (v := ⟨name, .value⟩) (c := argVar)
        (ρ := ρ.env) (u := v) hσwf hfresh_decls rfl
      have hag_env := Spec.argsEnv_agreeOn
        (ρ₁ := VerifM.Env.withEnv ρ₁ (σ'.subst.eval ρ₁.env))
        (ρ₂ := VerifM.Env.withEnv ρ ((σ.subst.eval ρ.env).updateConst .value name v))
        (by simpa [VerifM.Env.agreeOn, VerifM.Env.withEnv, σ', FiniteSubst.rename] using hag_rename)
        rest vs' (by simp [List.length_map] at hlen_rest; omega)
      ipure_intro
      refine ⟨σ'', argVar :: argVars', st', ρ', hΨ, hσ''wf, hσ''domwf,
        Signature.Subset.trans hst_st₂ hdsub',
        VerifM.Env.agreeOn_trans
          (VerifM.Env.agreeOn_update_fresh (ρ := ρ) (c := argVar) (u := v) hfresh_decls)
          (VerifM.Env.agreeOn_mono hst_st₂ hragree'),
        howns.trans hst₂_owns, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [σ', FiniteSubst.rename, Signature.ofVars, Spec.argVars,
               Signature.declVars, Signature.declVar] using hdom_sub
      · simpa [σ', FiniteSubst.rename, Spec.argsEnv, Spec.argVars, Signature.declVars,
               Signature.declVar, VerifM.Env.withEnv, VerifM.Env.agreeOn] using
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

theorem implement_correct (Θ : TinyML.TypeEnv) (s : Spec) (body : List FOL.Const → VerifM (Term .value))
    (st : TransState) (ρ : VerifM.Env) (vs : List Runtime.Val) (Φ : Runtime.Val → iProp) (R : iProp) :
    s.wfIn Signature.empty →
    VerifM.eval (Spec.implement s body) st ρ (fun _ _ _ => True) →
    (∀ (argVars : List FOL.Const) (st' : TransState) (ρ' : VerifM.Env) (Q : iProp),
      (∀ v ∈ argVars, v ∈ st'.decls.consts) →
      (∀ v ∈ argVars, v.sort = .value) →
      List.Forall₂ (fun av val => ρ'.env.consts .value av.name = val) argVars vs →
      VerifM.eval (body argVars) st' ρ'
        (fun result st'' ρ'' =>
          ∀ (S : iProp), result.wfIn st''.decls →
            st''.sl ρ'' ∗ Q ∗ ((TinyML.ValHasType Θ (result.eval ρ''.env) s.retTy -∗ Φ (result.eval ρ''.env)) -∗ S) ⊢ S) →
      st'.sl ρ' ∗ Q ⊢ R) →
    st.sl ρ ∗ TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd) ∗ PredTrans.apply (fun r => TinyML.ValHasType Θ r s.retTy -∗ Φ r) s.pred
      (Spec.argsEnv VerifM.Env.empty s.args vs) ⊢ R := by
  intro hswf heval hbody
  simp only [Spec.implement] at heval
  have hb := VerifM.eval_bind _ _ _ _ heval
  iintro H
  icases H with ⟨Howns, Hvals, Happ⟩
  iintuitionistic Hvals
  ihave %hlen_vals := TinyML.ValsHaveTypes.length_eq $$ Hvals
  ihave Hdecl := declareImplArgs_correct Θ s.args vs FiniteSubst.id st ρ _
      (FiniteSubst.id_wf st.decls)
      (by simpa [Signature.ofVars] using Signature.wf_empty) hb $$ Hvals
  ipure Hdecl
  obtain ⟨σ', argVars, st', ρ', hΨ, hσ'wf, hσ'domwf, hdsub, hragree, howns, hdom_sub, hagree,
    hmem_decls, hsorts, hlookups⟩ := Hdecl
  have hag_empty : VerifM.Env.agreeOn ((Signature.ofVars FiniteSubst.id.dom).declVars (Spec.argVars s.args))
      (Spec.argsEnv VerifM.Env.empty s.args vs)
      (Spec.argsEnv (VerifM.Env.withEnv ρ (FiniteSubst.id.subst.eval ρ.env)) s.args vs) :=
    Spec.argsEnv_agreeOn (Δ := Signature.empty)
      (ρ₁ := VerifM.Env.empty)
      (ρ₂ := VerifM.Env.withEnv ρ (FiniteSubst.id.subst.eval ρ.env))
      (by exact ⟨nofun, nofun, nofun, nofun⟩) s.args vs
      (by
        simp [List.length_map] at hlen_vals
        omega)
  have hst'_wf : st'.decls.wf := (VerifM.eval.wf hΨ).namesDisjoint
  iapply (show st'.sl ρ' ∗
        PredTrans.apply (fun r => TinyML.ValHasType Θ r s.retTy -∗ Φ r) s.pred
          (VerifM.Env.withEnv ρ' (σ'.subst.eval ρ'.env)) ⊢ R from
    PredTrans.implement_correct s.pred σ' (body argVars) st' ρ'
      (fun r => TinyML.ValHasType Θ r s.retTy -∗ Φ r) R
      (PredTrans.wfIn_mono hswf (Signature.Subset.ofVars hdom_sub) hσ'domwf)
      hσ'domwf hσ'wf hΨ
      (fun st'' ρ'' Q hdsub' hragree' hbody_eval => by
        apply hbody argVars st'' ρ'' Q
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
  · iapply (show st.sl ρ' ⊢ st'.sl ρ' by simp [howns, TransState.sl])
    iapply (show st.sl ρ ⊢ st.sl ρ' by
      simpa [TransState.sl] using
        (SpatialContext.interp_env_agree (VerifM.eval.wf heval).ownsWf hragree).1)
    iexact Howns
  · iapply (PredTrans.apply_env_agree hswf (VerifM.Env.agreeOn_trans hag_empty (VerifM.Env.agreeOn_symm hagree)))
    iexact Happ

end ImplementCorrectness
end Spec

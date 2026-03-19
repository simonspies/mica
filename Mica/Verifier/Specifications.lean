import Mica.TinyML.Expr
import Mica.TinyML.Typing
import Mica.TinyML.WeakestPre
import Mica.FOL.Printing
import Mica.Verifier.Monad
import Mica.Verifier.Assertions
import Mica.Verifier.Utils
import Mica.Verifier.PredicateTransformers
import Mica.Base.Fresh
import Mathlib.Data.Finmap

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
  args    : List (String × TinyML.Type_)
  retTy   : TinyML.Type_
  pred    : PredTrans

-- ---------------------------------------------------------------------------
-- Printers
-- ---------------------------------------------------------------------------

def SpecPredicate.toStringHum (s : SpecPredicate) : String :=
  MultiPred.toStringHum (Assertion.toStringHum (Pred.toStringHum (Assertion.toStringHum (fun () => "()")))) s

-- ---------------------------------------------------------------------------
-- Well-formedness
-- ---------------------------------------------------------------------------

/-- The list of SMT variables corresponding to a spec's arguments. -/
def Spec.argVars (args : List (String × TinyML.Type_)) : List Var :=
  args.map fun (name, _) => ⟨name, .value⟩

/-- Build an environment binding each argument name to its value, left-to-right.
    Later arguments shadow earlier ones with the same name. -/
def Spec.argsEnv (ρ : Env) : List (String × TinyML.Type_) → List TinyML.Val → Env
  | [], _ | _, [] => ρ
  | (name, _) :: rest, v :: vs => Spec.argsEnv (ρ.update .value name v) rest vs

def Spec.isPrecondFor (f : TinyML.Val) (s : Spec) : Prop :=
  ∀ (vs : List TinyML.Val), TinyML.ValsHaveTypes vs (s.args.map Prod.snd) →
    ∀ (Φ : TinyML.Val → Prop),
      PredTrans.apply (fun r => TinyML.ValHasType r s.retTy → Φ r) s.pred
        (Spec.argsEnv Env.empty s.args vs) →
      wp (TinyML.Expr.app (.val f) (vs.map fun v => .val v)) Φ

/-- A spec is well-formed when its predicate transformer is well-formed in the
    context extended with all argument variables. -/
def Spec.wfIn (spec : Spec) (decls : List Var) : Prop :=
  PredTrans.wfIn (Spec.argVars spec.args ++ decls) spec.pred

def Spec.checkWf (spec : Spec) (decls : List Var) : Except String Unit :=
  PredTrans.checkWf (Spec.argVars spec.args ++ decls) spec.pred

theorem Spec.checkWf_ok {spec : Spec} {decls : List Var}
    (h : spec.checkWf decls = .ok ()) : spec.wfIn decls :=
  PredTrans.checkWf_ok h

theorem Spec.wfIn_mono {spec : Spec} {decls decls' : List Var}
    (h : spec.wfIn decls) (hsub : decls ⊆ decls') : spec.wfIn decls' :=
  PredTrans.wfIn_mono h (by
    intro x hx; cases List.mem_append.mp hx with
    | inl h => exact List.mem_append_left _ h
    | inr h => exact List.mem_append_right _ (hsub h))

-- ---------------------------------------------------------------------------
-- Type constraints
-- ---------------------------------------------------------------------------

/-- Generate SMT formulas asserting that a value-sorted term has a given TinyML type.
    For `int`: `is-of_int(t)`, for `bool`: `is-of_bool(t)`,
    for `tuple ts`: `is-of_tuple(t)` plus recursive constraints on elements. -/
def typeConstraints (ty : TinyML.Type_) (t : Term .value) : List Formula :=
  match ty with
  | .int   => [.unpred .isInt t]
  | .bool  => [.unpred .isBool t]
  | .tuple ts =>
      .unpred .isTuple t ::
      typeConstraintsList ts (.unop .toValList t)
  | _ => []
where
  typeConstraintsList (ts : List TinyML.Type_) (tl : Term .vallist) : List Formula :=
    match ts with
    | [] => []
    | ty :: rest =>
        typeConstraints ty (.unop .vhead tl) ++
        typeConstraintsList rest (.unop .vtail tl)

mutual
  /-- All formulas in `typeConstraints ty t` only reference free variables of `t`. -/
  theorem typeConstraints_wfIn {ty : TinyML.Type_} {t : Term .value} {Δ : List Var}
      (ht : t.wfIn Δ) : ∀ φ ∈ typeConstraints ty t, φ.wfIn Δ := by
    cases ty with
    | int =>
      simp [typeConstraints]
      intro w hw; simp [Formula.freeVars] at hw; exact ht w hw
    | bool =>
      simp [typeConstraints]
      intro w hw; simp [Formula.freeVars] at hw; exact ht w hw
    | tuple ts =>
      simp only [typeConstraints]
      intro φ hφ
      cases hφ with
      | head =>
        intro w hw; simp [Formula.freeVars] at hw; exact ht w hw
      | tail _ hφ =>
        exact typeConstraintsList_wfIn (by intro w hw; simp [Term.freeVars] at hw; exact ht w hw) φ hφ
    | _ => simp [typeConstraints]

  theorem typeConstraintsList_wfIn {ts : List TinyML.Type_} {tl : Term .vallist} {Δ : List Var}
      (htl : tl.wfIn Δ) : ∀ φ ∈ typeConstraints.typeConstraintsList ts tl, φ.wfIn Δ := by
    cases ts with
    | nil => simp [typeConstraints.typeConstraintsList]
    | cons ty rest =>
      simp only [typeConstraints.typeConstraintsList]
      intro φ hφ
      cases List.mem_append.mp hφ with
      | inl h =>
        exact typeConstraints_wfIn (by intro w hw; simp [Term.freeVars] at hw; exact htl w hw) φ h
      | inr h =>
        exact typeConstraintsList_wfIn (by intro w hw; simp [Term.freeVars] at hw; exact htl w hw) φ h
end

mutual
  /-- If `ValHasType v ty` and `t.eval ρ = v`, then all formulas in `typeConstraints ty t` hold. -/
  theorem typeConstraints_hold {ty : TinyML.Type_} {t : Term .value} {ρ : Env}
      {v : TinyML.Val} (ht : t.eval ρ = v) (hty : TinyML.ValHasType v ty) :
      ∀ φ ∈ typeConstraints ty t, φ.eval ρ := by
    cases hty with
    | int n =>
      intro φ hφ; simp [typeConstraints] at hφ; subst hφ
      simp [Formula.eval, ht]
    | bool b =>
      intro φ hφ; simp [typeConstraints] at hφ; subst hφ
      simp [Formula.eval, ht]
    | tuple hvs =>
      simp only [typeConstraints]
      intro φ hφ
      cases hφ with
      | head =>
        simp [Formula.eval, ht]
      | tail _ hφ =>
        exact typeConstraintsList_hold
          (by simp [Term.eval, UnOp.eval, ht]) hvs φ hφ
    | any => simp [typeConstraints]
    | _ => simp [typeConstraints]

  theorem typeConstraintsList_hold {ts : List TinyML.Type_} {tl : Term .vallist} {ρ : Env}
      {vs : List TinyML.Val} (htl : tl.eval ρ = vs) (hty : TinyML.ValsHaveTypes vs ts) :
      ∀ φ ∈ typeConstraints.typeConstraintsList ts tl, φ.eval ρ := by
    cases hty with
    | nil => simp [typeConstraints.typeConstraintsList]
    | cons hv hvs =>
      simp only [typeConstraints.typeConstraintsList]
      intro φ hφ
      cases List.mem_append.mp hφ with
      | inl h =>
        exact typeConstraints_hold (by simp [Term.eval, UnOp.eval, htl]) hv φ h
      | inr h =>
        exact typeConstraintsList_hold (by simp [Term.eval, UnOp.eval, htl]) hvs φ h
end

-- ---------------------------------------------------------------------------
-- Spec verifier operations
-- ---------------------------------------------------------------------------

/-- Declare argument variables, check types, and assume equalities for a spec call.
    Returns the updated substitution. -/
def Spec.declareArgs (σ : FiniteSubst) :
    List (String × TinyML.Type_) → List (TinyML.Type_ × Term .value) → VerifM FiniteSubst
  | [], [] => pure σ
  | (name, ty) :: rest, (targ, sarg) :: sargs => do
    if targ.sub ty then pure ()
    else VerifM.fatal s!"type mismatch in call to spec"
    let argVar ← VerifM.decl (some name) .value
    let σ' := σ.rename ⟨name, .value⟩ argVar.name
    VerifM.assume (.eq .value (.var .value argVar.name) sarg)
    Spec.declareArgs σ' rest sargs
  | _, _ => VerifM.fatal "wrong number of arguments"

/-- Full call protocol for a spec: declare argument variables, assume they equal the
    compiled argument terms, check argument types, then invoke `PredTrans.call`. -/
def Spec.call (σ : FiniteSubst) (s : Spec) (sargs : List (TinyML.Type_ × Term .value)) :
    VerifM (TinyML.Type_ × Term .value) := do
  let σ' ← Spec.declareArgs σ s.args sargs
  let result ← PredTrans.call σ' s.pred
  pure (s.retTy, result)

/-- Declare implementation argument variables: for each `(name, ty)` in `args`,
    declare a fresh variable, assume its type constraints, and rename in `σ`.
    Returns the final substitution and the list of declared argument variables. -/
def Spec.declareImplArgs (σ : FiniteSubst) :
    List (String × TinyML.Type_) → VerifM (FiniteSubst × List Var)
  | [] => pure (σ, [])
  | (name, ty) :: rest => do
    let argVar ← VerifM.decl (some name) .value
    VerifM.assumeAll (typeConstraints ty (.var .value argVar.name))
    let σ' := σ.rename ⟨name, .value⟩ argVar.name
    let (σ'', vars) ← Spec.declareImplArgs σ' rest
    pure (σ'', argVar :: vars)

/-- Full implementation protocol for a spec: declare argument variables,
    assume type constraints, then invoke `PredTrans.implement`. Dual to `Spec.call`. -/
def Spec.implement (s : Spec) (body : List Var → VerifM (Term .value)) : VerifM Unit := do
  let (σ, argVars) ← Spec.declareImplArgs FiniteSubst.id s.args
  PredTrans.implement σ s.pred (body argVars)

-- ---------------------------------------------------------------------------
-- SpecMap
-- ---------------------------------------------------------------------------

abbrev SpecMap := Finmap (fun _ : TinyML.Var => Spec)

def SpecMap.satisfiedBy (S : SpecMap) (γ : TinyML.Subst) : Prop :=
  ∀ x s, S.lookup x = some s →
    ∃ f, γ x = some f ∧ s.isPrecondFor f

def SpecMap.wfIn (S : SpecMap) (decls : List Var) : Prop :=
  ∀ f spec, S.lookup f = some spec → spec.wfIn decls

theorem SpecMap.wfIn_mono {S : SpecMap} {decls decls' : List Var}
    (h : S.wfIn decls) (hsub : decls ⊆ decls') : S.wfIn decls' :=
  fun f spec hlookup => Spec.wfIn_mono (h f spec hlookup) hsub

theorem SpecMap.wfIn_erase {S : SpecMap} {x : TinyML.Var} {decls : List Var}
    (h : S.wfIn decls) : SpecMap.wfIn (Finmap.erase x S) decls := by
  intro f spec hlookup
  by_cases hfx : f = x
  · subst hfx; rw [Finmap.lookup_erase] at hlookup; exact absurd hlookup (by simp)
  · rw [Finmap.lookup_erase_ne hfx] at hlookup
    exact h f spec hlookup

def SpecMap.insert' (S : SpecMap) (b : TinyML.Binder) (spec : Spec) : SpecMap :=
  match b with
  | .named x => S.insert x spec
  | .none => S

theorem SpecMap.satisfiedBy_insert {S : SpecMap} {γ : TinyML.Subst}
    {x : TinyML.Var} {fval : TinyML.Val} {spec : Spec}
    (hS : S.satisfiedBy γ) (hγ : γ x = some fval) (hf : spec.isPrecondFor fval) :
    SpecMap.satisfiedBy (Finmap.insert x spec S) γ := by
  intro y s' hlookup
  by_cases hyx : y = x
  · subst hyx; rw [Finmap.lookup_insert] at hlookup; simp at hlookup; subst hlookup
    exact ⟨fval, hγ, hf⟩
  · rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
    exact hS y s' hlookup

theorem SpecMap.wfIn_insert {S : SpecMap} {x : TinyML.Var} {spec : Spec} {decls : List Var}
    (hS : S.wfIn decls) (hs : spec.wfIn decls) : SpecMap.wfIn (Finmap.insert x spec S) decls := by
  intro y s' hlookup
  by_cases hyx : y = x
  · subst hyx; rw [Finmap.lookup_insert] at hlookup; simp at hlookup; subst hlookup; exact hs
  · rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup; exact hS y s' hlookup

theorem SpecMap.satisfiedBy_insert' {S : SpecMap} {γ : TinyML.Subst}
    {b : TinyML.Binder} {fval : TinyML.Val} {spec : Spec}
    (hS : S.satisfiedBy γ)
    (hγ : ∀ x, b = .named x → γ x = some fval)
    (hf : spec.isPrecondFor fval) :
    SpecMap.satisfiedBy (S.insert' b spec) γ := by
  cases b with
  | named x => exact SpecMap.satisfiedBy_insert hS (hγ x rfl) hf
  | none => exact hS

theorem SpecMap.wfIn_insert' {S : SpecMap} {b : TinyML.Binder} {spec : Spec} {decls : List Var}
    (hS : S.wfIn decls) (hs : spec.wfIn decls) : SpecMap.wfIn (S.insert' b spec) decls := by
  cases b with
  | named x => exact SpecMap.wfIn_insert hS hs
  | none => exact hS

theorem SpecMap.empty_satisfiedBy (γ : TinyML.Subst) :
    SpecMap.satisfiedBy (∅ : SpecMap) γ := by
  intro x s h; simp [Finmap.lookup_empty] at h

theorem SpecMap.empty_wfIn (decls : List Var) :
    SpecMap.wfIn (∅ : SpecMap) decls := by
  intro f spec h; simp [Finmap.lookup_empty] at h

theorem SpecMap.satisfiedBy_erase {S : SpecMap} {γ : TinyML.Subst} {x : TinyML.Var} {v : TinyML.Val}
    (h : S.satisfiedBy γ) : SpecMap.satisfiedBy (Finmap.erase x S) (TinyML.Subst.update γ x v) := by
  intro y s hlookup
  by_cases hyx : y = x
  · subst hyx; rw [Finmap.lookup_erase] at hlookup; exact absurd hlookup (by simp)
  · rw [Finmap.lookup_erase_ne hyx] at hlookup
    obtain ⟨fval, hγ, hisPrecond⟩ := h y s hlookup
    exact ⟨fval, by simp [TinyML.Subst.update, hyx, hγ], hisPrecond⟩

-- ---------------------------------------------------------------------------
-- Spec correctness
-- ---------------------------------------------------------------------------

private theorem argVars_cons_perm {name : String}
    {rest : List (String × TinyML.Type_)} {dom : List Var} {x : Var}
    (hx : x ∈ (⟨name, .value⟩ :: Spec.argVars rest ++ dom)) :
    x ∈ (Spec.argVars rest ++ ⟨name, .value⟩ :: dom) := by
  simp only [Spec.argVars, List.cons_append, List.mem_cons,
    List.mem_append, List.mem_map] at hx ⊢
  rcases hx with rfl | ⟨a, ha, rfl⟩ | hmem
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl ⟨a, ha, rfl⟩
  · exact Or.inr (Or.inr hmem)

/-- `argsEnv` preserves `agreeOn`: if two base envs agree on `Δ`,
    then after applying the same updates, they agree on `argVars args ++ Δ`. -/
theorem Spec.argsEnv_agreeOn {Δ : List Var} {ρ₁ ρ₂ : Env}
    (h : Env.agreeOn Δ ρ₁ ρ₂) :
    ∀ (args : List (String × TinyML.Type_)) (vals : List TinyML.Val),
    args.length ≤ vals.length →
    Env.agreeOn (Spec.argVars args ++ Δ)
      (Spec.argsEnv ρ₁ args vals) (Spec.argsEnv ρ₂ args vals) := by
  intro args
  induction args generalizing Δ ρ₁ ρ₂ with
  | nil => intro vals _; simp [Spec.argVars, Spec.argsEnv]; exact h
  | cons arg rest ih =>
    intro vals hlen
    obtain ⟨name, ty⟩ := arg
    cases vals with
    | nil => simp at hlen
    | cons v vs =>
      simp only [Spec.argsEnv]
      have := ih (Env.agreeOn_update (τ := .value) (x := name) (v := v) h) vs
        (by simp [List.length] at hlen ⊢; omega)
      exact Env.agreeOn_mono (fun _ => argVars_cons_perm) this

/-- Correctness of `declareArgs`: after processing all arguments, the resulting
    substitution is well-formed, types match, and the env agrees with `argsEnv`. -/
theorem Spec.declareArgs_correct :
    ∀ (args : List (String × TinyML.Type_)) (sargs : List (TinyML.Type_ × Term .value))
      (σ : FiniteSubst) (st : TransState) (ρ : Env)
      (Ψ : FiniteSubst → TransState → Env → Prop),
    σ.wf st.decls →
    (∀ p ∈ sargs, (p : TinyML.Type_ × Term .value).2.wfIn st.decls) →
    VerifM.eval (Spec.declareArgs σ args sargs) st ρ Ψ →
    ∃ σ' st' ρ', Ψ σ' st' ρ' ∧
      σ'.wf st'.decls ∧
      TinyML.Type_.SubList (sargs.map Prod.fst) (args.map Prod.snd) ∧
      (∀ x ∈ Spec.argVars args ++ σ.dom, x ∈ σ'.dom) ∧
      Env.agreeOn (Spec.argVars args ++ σ.dom) (σ'.subst.eval ρ')
        (Spec.argsEnv (σ.subst.eval ρ) args (sargs.map fun p => p.2.eval ρ)) := by
  intro args
  induction args with
  | nil =>
    intro sargs σ st ρ Ψ hσwf hsargs heval
    cases sargs with
    | nil =>
      simp [Spec.declareArgs] at heval
      have := VerifM.eval_ret heval
      exact ⟨σ, st, ρ, this, hσwf, .nil, fun x hx => hx,
        by simp [Spec.argVars, Spec.argsEnv]; exact Env.agreeOn_refl⟩
    | cons _ _ =>
      simp [Spec.declareArgs] at heval
      exact (VerifM.eval_fatal heval).elim
  | cons arg rest ih =>
    intro sargs σ st ρ Ψ hσwf hsargs heval
    obtain ⟨name, ty⟩ := arg
    cases sargs with
    | nil =>
      simp [Spec.declareArgs] at heval
      exact (VerifM.eval_fatal heval).elim
    | cons sarg_hd sargs_rest =>
      obtain ⟨targ, sarg⟩ := sarg_hd
      simp only [Spec.declareArgs] at heval
      by_cases hsub_ty : targ.sub ty = true
      · simp [hsub_ty] at heval
        have hbind := VerifM.eval_bind _ _ _ _ heval
        have hret := VerifM.eval_ret hbind
        have hb2 := VerifM.eval_bind _ _ _ _ hret
        have hdecl := VerifM.eval_decl hb2
        set argVar := st.freshVar (some name) .value
        have hfresh_decls : argVar.name ∉ st.decls.map Var.name :=
          fresh_not_mem (addNumbers name) (st.decls.map Var.name) (addNumbers_injective _)
        have hfresh_range : ⟨argVar.name, Srt.value⟩ ∉ σ.range := by
          intro hmem; exact hfresh_decls (List.mem_map.mpr ⟨⟨argVar.name, .value⟩, hσwf.2 hmem, rfl⟩)
        specialize hdecl (sarg.eval ρ)
        set σ' := σ.rename ⟨name, .value⟩ argVar.name
        have hσ'wf : σ'.wf (argVar :: st.decls) := FiniteSubst.rename_wf hσwf hfresh_range
        have hsarg_wf : sarg.wfIn st.decls := hsargs (targ, sarg) (List.mem_cons_self ..)
        have heq_wf : (Formula.eq Srt.value (Term.var .value argVar.name) sarg).wfIn
            (argVar :: st.decls) := by
          intro w hw
          simp only [Formula.freeVars, Term.freeVars] at hw
          cases hw with
          | head => exact .head _
          | tail _ hw => exact .tail _ (hsarg_wf w hw)
        have heq_holds : (Formula.eq Srt.value (Term.var .value argVar.name) sarg).eval
            (ρ.update .value argVar.name (sarg.eval ρ)) := by
          simp only [Formula.eval, Term.eval, Env.lookup_update_same]
          exact Term.eval_env_agree hsarg_wf (agreeOn_update_fresh hfresh_decls)
        have hb3 := VerifM.eval_bind _ _ _ _ hdecl
        have hassume := VerifM.eval_assume hb3 heq_wf heq_holds
        set ρ₁ := ρ.update .value argVar.name (sarg.eval ρ)
        have hsargs_rest : ∀ p ∈ sargs_rest, (p : TinyML.Type_ × Term .value).2.wfIn
            (argVar :: st.decls) := by
          intro p hp
          exact fun w hw => List.mem_cons_of_mem _ (hsargs p (List.mem_cons_of_mem _ hp) w hw)
        have hsargs_eval : sargs_rest.map (fun p => p.2.eval ρ₁) =
            sargs_rest.map (fun p => p.2.eval ρ) := by
          apply List.map_congr_left
          intro p hp
          exact Term.eval_env_agree
            (hsargs p (List.mem_cons_of_mem _ hp))
            (Env.agreeOn_symm (agreeOn_update_fresh hfresh_decls))
        obtain ⟨σ'', st'', ρ'', hΨ, hσ''wf, hsublist, hdom_sub, hagree⟩ :=
          ih sargs_rest σ' _ ρ₁ Ψ hσ'wf hsargs_rest hassume
        refine ⟨σ'', st'', ρ'', hΨ, hσ''wf,
          .cons (TinyML.Type_.sub_iff.mp hsub_ty) hsublist, ?_, ?_⟩
        · intro x hx
          apply hdom_sub
          simp only [σ', FiniteSubst.rename]
          exact argVars_cons_perm hx
        · have hag_rename := @FiniteSubst.rename_agreeOn σ ⟨name, .value⟩ argVar.name
            ρ (sarg.eval ρ) hσwf.1 hfresh_range
          have hlen : rest.length ≤ sargs_rest.length := by
            have := TinyML.Type_.SubList.length_eq hsublist
            simp [List.length_map] at this; omega
          have hag_env := Spec.argsEnv_agreeOn hag_rename rest
            (sargs_rest.map fun p => p.2.eval ρ) (by simp [List.length_map]; omega)
          simp only [σ', FiniteSubst.rename] at hagree
          rw [hsargs_eval] at hagree
          have hagree' := Env.agreeOn_trans hagree hag_env
          exact Env.agreeOn_mono (fun _ => argVars_cons_perm) hagree'
      · rw [if_neg hsub_ty] at heval
        have hb := VerifM.eval_bind _ _ _ _ heval
        exact (VerifM.eval_fatal hb).elim

theorem Spec.call_correct (s : Spec) (σ : FiniteSubst) (sargs : List (TinyML.Type_ × Term .value))
    (st : TransState) (ρ : Env)
    (Ψ : (TinyML.Type_ × Term .value) → TransState → Env → Prop)
    (Φ : TinyML.Val → Prop) :
    s.pred.wfIn (Spec.argVars s.args ++ σ.dom) →
    σ.wf st.decls →
    (∀ p ∈ sargs, (p : TinyML.Type_ × Term .value).2.wfIn st.decls) →
    VerifM.eval (Spec.call σ s sargs) st ρ Ψ →
    (∀ v st' ρ' t, Ψ (s.retTy, t) st' ρ' → t.wfIn st'.decls → t.eval ρ' = v → Φ v) →
    TinyML.Type_.SubList (sargs.map Prod.fst) (s.args.map Prod.snd) ∧
    PredTrans.apply Φ s.pred
      (Spec.argsEnv (σ.subst.eval ρ) s.args (sargs.map fun p => p.2.eval ρ)) := by
  intro hwf hσwf hsargs heval hΨ
  simp only [Spec.call] at heval
  have hb := VerifM.eval_bind _ _ _ _ heval
  obtain ⟨σ', st', ρ', hΨ', hσ'wf, hsublist, hdom_sub, hagree⟩ :=
    Spec.declareArgs_correct s.args sargs σ st ρ _ hσwf hsargs hb
  constructor
  · exact hsublist
  · have hb2 := VerifM.eval_bind _ _ _ _ hΨ'
    have hcall := PredTrans.call_correct s.pred σ' st' ρ' _ Φ
      (PredTrans.wfIn_mono hwf hdom_sub) hσ'wf hb2
      (fun v st'' ρ'' t hΨ'' htwf hteval => by
        have hret := VerifM.eval_ret hΨ''
        exact hΨ v st'' ρ'' t hret htwf hteval)
    exact PredTrans.apply_env_agree hwf hagree hcall

/-- Correctness of `declareImplArgs`: after processing all arguments, the resulting
    substitution is well-formed, all argVars are in decls with sort `.value`,
    and the env agrees with `argsEnv`. -/
theorem Spec.declareImplArgs_correct :
    ∀ (args : List (String × TinyML.Type_)) (vs : List TinyML.Val)
      (σ : FiniteSubst) (st : TransState) (ρ : Env)
      (Ψ : (FiniteSubst × List Var) → TransState → Env → Prop),
    σ.wf st.decls →
    TinyML.ValsHaveTypes vs (args.map Prod.snd) →
    VerifM.eval (Spec.declareImplArgs σ args) st ρ Ψ →
    ∃ σ' argVars st' ρ', Ψ (σ', argVars) st' ρ' ∧
      σ'.wf st'.decls ∧
      st.decls ⊆ st'.decls ∧
      ρ.agreeOn st.decls ρ' ∧
      (∀ x ∈ Spec.argVars args ++ σ.dom, x ∈ σ'.dom) ∧
      Env.agreeOn (Spec.argVars args ++ σ.dom) (σ'.subst.eval ρ')
        (Spec.argsEnv (σ.subst.eval ρ) args vs) ∧
      (∀ v ∈ argVars, v ∈ st'.decls) ∧
      (∀ v ∈ argVars, v.sort = .value) ∧
      List.Forall₂ (fun av val => ρ'.lookup .value av.name = val) argVars vs := by
  intro args
  induction args with
  | nil =>
    intro vs σ st ρ Ψ hσwf hvs heval
    cases hvs with
    | nil =>
      simp [Spec.declareImplArgs] at heval
      have := VerifM.eval_ret heval
      exact ⟨σ, [], st, ρ, this, hσwf, List.Subset.refl _, Env.agreeOn_refl, fun x hx => hx,
        by simp [Spec.argVars, Spec.argsEnv]; exact Env.agreeOn_refl,
        nofun,
        nofun,
        .nil⟩
  | cons arg rest ih =>
    intro vs σ st ρ Ψ hσwf hvs heval
    obtain ⟨name, ty⟩ := arg
    cases hvs with
    | cons hv hvs_rest =>
      rename_i v vs'
      simp only [Spec.declareImplArgs] at heval
      have hb := VerifM.eval_bind _ _ _ _ heval
      have hdecl := VerifM.eval_decl hb
      set argVar := st.freshVar (some name) .value
      specialize hdecl v
      have hfresh_decls : argVar.name ∉ st.decls.map Var.name :=
        fresh_not_mem (addNumbers name) (st.decls.map Var.name) (addNumbers_injective _)
      have hfresh_range : ⟨argVar.name, Srt.value⟩ ∉ σ.range := by
        intro hmem; exact hfresh_decls (List.mem_map.mpr ⟨⟨argVar.name, .value⟩, hσwf.2 hmem, rfl⟩)
      set st₁ : TransState := { st with decls := argVar :: st.decls }
      set ρ₁ := ρ.update .value argVar.name v
      -- Peel off assumeAll
      have hvar_wf : (Term.var Srt.value argVar.name).wfIn st₁.decls := by
        intro w hw; simp [Term.freeVars] at hw; subst hw; exact List.mem_cons_self ..
      have hvar_eval : (Term.var Srt.value argVar.name).eval ρ₁ = v := by
        simp [Term.eval, ρ₁]
      have hassume_bind := VerifM.eval_bind _ _ _ _ hdecl
      obtain ⟨st₂, hst₂_decls, hdecl₂⟩ := VerifM.eval_assumeAll hassume_bind
        (fun φ hφ => typeConstraints_wfIn hvar_wf φ hφ)
        (fun φ hφ => typeConstraints_hold hvar_eval hv φ hφ)
      set σ' := σ.rename ⟨name, .value⟩ argVar.name
      have hσ'wf : σ'.wf st₁.decls := FiniteSubst.rename_wf hσwf hfresh_range
      have hσ'wf₂ : σ'.wf st₂.decls := hst₂_decls ▸ hσ'wf
      have hst_st₂ : st.decls ⊆ st₂.decls := by
        rw [hst₂_decls]; exact List.subset_cons_of_subset _ (List.Subset.refl _)
      obtain ⟨σ'', argVars', st', ρ', hΨ, hσ''wf, hdsub', hragree', hdom_sub, hagree, hmem_decls,
        hsorts, hlookups⟩ := ih vs' σ' st₂ ρ₁ _ hσ'wf₂ hvs_rest hdecl₂
      refine ⟨σ'', argVar :: argVars', st', ρ', hΨ, hσ''wf,
        List.Subset.trans hst_st₂ hdsub', ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- ρ.agreeOn st.decls ρ'
      · intro w hw
        have h₁ := hragree' w (hst_st₂ hw)
        have h₂ := @agreeOn_update_fresh ρ argVar v st.decls hfresh_decls w hw
        rw [h₂]; exact h₁
      -- dom inclusion
      · intro x hx; apply hdom_sub
        simp only [σ', FiniteSubst.rename]
        exact argVars_cons_perm hx
      -- env agree
      · have hag_rename := @FiniteSubst.rename_agreeOn σ ⟨name, .value⟩ argVar.name
            ρ v hσwf.1 hfresh_range
        have hag_env := Spec.argsEnv_agreeOn hag_rename rest vs' (by
            have := hvs_rest.length_eq
            simp [List.length_map] at this; omega)
        simp only [σ', FiniteSubst.rename] at hagree
        exact Env.agreeOn_mono (fun _ => argVars_cons_perm)
          (Env.agreeOn_trans hagree hag_env)
      -- argVars all in decls
      · intro w hw
        cases List.mem_cons.mp hw with
        | inl h => subst h; exact hdsub' (hst₂_decls ▸ List.mem_cons_self ..)
        | inr h => exact hmem_decls w h
      -- sorts
      · intro w hw
        cases List.mem_cons.mp hw with
        | inl h => subst h; rfl
        | inr h => exact hsorts w h
      -- lookups
      · constructor
        · have h1 := hragree' ⟨argVar.name, .value⟩ (hst₂_decls ▸ List.mem_cons_self ..)
          simp [ρ₁, Env.lookup_update_same] at h1
          exact h1.symm
        · exact hlookups

theorem Spec.implement_correct (s : Spec) (body : List Var → VerifM (Term .value))
    (st : TransState) (ρ : Env) (vs : List TinyML.Val) (Φ : TinyML.Val → Prop) (R : Prop) :
    s.wfIn [] →
    TinyML.ValsHaveTypes vs (s.args.map Prod.snd) →
    VerifM.eval (Spec.implement s body) st ρ (fun _ _ _ => True) →
    PredTrans.apply Φ s.pred (Spec.argsEnv Env.empty s.args vs) →
    (∀ argVars st' ρ',
      (∀ v ∈ argVars, v ∈ st'.decls) →
      (∀ v ∈ argVars, v.sort = .value) →
      List.Forall₂ (fun av val => ρ'.lookup .value av.name = val) argVars vs →
      VerifM.eval (body argVars) st' ρ'
        (fun result st'' ρ'' => result.wfIn st''.decls → Φ (result.eval ρ'')) → R) →
    R := by
  intro hswf hvs heval happly hR
  simp only [Spec.implement] at heval
  have hb := VerifM.eval_bind _ _ _ _ heval
  obtain ⟨σ', argVars, st', ρ', hΨ, hσ'wf, hdsub, hragree, hdom_sub, hagree,
    hmem_decls, hsorts, hlookups⟩ :=
    Spec.declareImplArgs_correct s.args vs FiniteSubst.id st ρ _ (FiniteSubst.id_wf st.decls) hvs hb
  -- Transport apply from argsEnv Env.empty to σ'.subst.eval ρ'
  have hag_empty : Env.agreeOn (Spec.argVars s.args ++ FiniteSubst.id.dom)
      (Spec.argsEnv Env.empty s.args vs)
      (Spec.argsEnv (FiniteSubst.id.subst.eval ρ) s.args vs) := by
    apply Spec.argsEnv_agreeOn
    · intro w hw; simp [FiniteSubst.id] at hw
    · have := hvs.length_eq
      simp [List.length_map] at this; omega
  have happly' : PredTrans.apply Φ s.pred (σ'.subst.eval ρ') :=
    PredTrans.apply_env_agree hswf
      (Env.agreeOn_trans hag_empty (Env.agreeOn_symm hagree)) happly
  -- hΨ is already `(PredTrans.implement σ' s.pred (body argVars)).eval st' ρ' ...`
  apply PredTrans.implement_correct s.pred σ' (body argVars) st' ρ' Φ R
    (PredTrans.wfIn_mono hswf hdom_sub) hσ'wf hΨ happly'
  -- Callback
  intro st'' ρ'' hdsub' hragree' hbody_eval
  apply hR argVars st'' ρ''
  · intro v hv; exact hdsub' (hmem_decls v hv)
  · exact hsorts
  · suffices ∀ (avs : List Var) (vals : List TinyML.Val),
        List.Forall₂ (fun av val => ρ'.lookup .value av.name = val) avs vals →
        (∀ v ∈ avs, v ∈ st'.decls) →
        (∀ v ∈ avs, v.sort = .value) →
        List.Forall₂ (fun av val => ρ''.lookup .value av.name = val) avs vals by
      exact this argVars vs hlookups hmem_decls hsorts
    intro avs vals hf
    induction hf with
    | nil => intros; exact .nil
    | cons hlk _ ih =>
      intro hmem hsrt
      constructor
      · have := hragree' _ (hmem _ (.head ..))
        rw [hsrt _ (.head ..)] at this; rw [← this]; exact hlk
      · exact ih (fun v hv => hmem v (.tail _ hv)) (fun v hv => hsrt v (.tail _ hv))
  · exact hbody_eval

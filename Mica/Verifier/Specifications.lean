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

-- ---------------------------------------------------------------------------
-- Printers
-- ---------------------------------------------------------------------------

def SpecPredicate.toStringHum (s : SpecPredicate) : String :=
  MultiPred.toStringHum (Assertion.toStringHum (Pred.toStringHum (Assertion.toStringHum (fun () => "()")))) s

-- ---------------------------------------------------------------------------
-- Well-formedness
-- ---------------------------------------------------------------------------

/-- The list of SMT variables corresponding to a spec's arguments. -/
def Spec.argVars (args : List (String × TinyML.Typ)) : List Var :=
  args.map fun (name, _) => ⟨name, .value⟩

/-- Build an environment binding each argument name to its value, left-to-right.
    Later arguments shadow earlier ones with the same name. -/
def Spec.argsEnv (ρ : Env) : List (String × TinyML.Typ) → List Runtime.Val → Env
  | [], _ | _, [] => ρ
  | (name, _) :: rest, v :: vs => Spec.argsEnv (ρ.updateConst .value name v) rest vs

def Spec.isPrecondFor (Θ : TinyML.TypeEnv) (f : Runtime.Val) (s : Spec) : iProp :=
  iprop (□ ∀ (Φ : Runtime.Val → iProp) (vs : List Runtime.Val),
      ⌜TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd)⌝ -∗
        PredTrans.apply (fun r => ⌜TinyML.ValHasType Θ r s.retTy⌝ -∗ Φ r) s.pred
          (Spec.argsEnv Env.empty s.args vs) -∗
        wp (Runtime.Expr.app (.val f) (vs.map fun v => .val v)) Φ)

/-- A spec is well-formed when its predicate transformer is well-formed in the
    context extended with all argument variables. -/
def Spec.wfIn (spec : Spec) (Δ : Signature) : Prop :=
  PredTrans.wfIn (Δ.declVars (Spec.argVars spec.args)) spec.pred

def Spec.checkWf (spec : Spec) (Δ : Signature) : Except String Unit :=
  PredTrans.checkWf (Δ.declVars (Spec.argVars spec.args)) spec.pred

theorem Spec.checkWf_ok {spec : Spec} {Δ : Signature}
    (h : spec.checkWf Δ = .ok ()) : spec.wfIn Δ :=
  PredTrans.checkWf_ok h

theorem Spec.wfIn_mono {spec : Spec} {Δ Δ' : Signature}
    (h : spec.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) :
    Spec.wfIn spec Δ' :=
  PredTrans.wfIn_mono h (Signature.Subset.declVars hsub (Spec.argVars spec.args))
    (Signature.wf_declVars hwf)

-- ---------------------------------------------------------------------------
-- Type constraints
-- ---------------------------------------------------------------------------

/-- Generate SMT formulas asserting that a value-sorted term has a given TinyML type.
    For `int`: `is-of_int(t)`, for `bool`: `is-of_bool(t)`,
    for `tuple ts`: `is-of_tuple(t)` plus recursive constraints on elements. -/
def typeConstraints (ty : TinyML.Typ) (t : Term .value) : List Formula :=
  match ty with
  | .int   => [.unpred .isInt t]
  | .bool  => [.unpred .isBool t]
  | .tuple ts =>
      .unpred .isTuple t ::
      typeConstraintsList ts (.unop .toValList t)
  | _ => []
where
  typeConstraintsList (ts : List TinyML.Typ) (tl : Term .vallist) : List Formula :=
    match ts with
    | [] => []
    | ty :: rest =>
        typeConstraints ty (.unop .vhead tl) ++
        typeConstraintsList rest (.unop .vtail tl)

mutual
  /-- All formulas in `typeConstraints ty t` only reference free variables of `t`. -/
  theorem typeConstraints_wfIn {ty : TinyML.Typ} {t : Term .value} {Δ : Signature}
      (ht : t.wfIn Δ) : ∀ φ ∈ typeConstraints ty t, φ.wfIn Δ := by
    cases ty with
    | int =>
      simp [typeConstraints]
      simp only [Formula.wfIn]; exact ht
    | bool =>
      simp [typeConstraints]
      simp only [Formula.wfIn]; exact ht
    | tuple ts =>
      simp only [typeConstraints]
      intro φ hφ
      cases hφ with
      | head =>
        simp only [Formula.wfIn]; exact ht
      | tail _ hφ =>
        exact typeConstraintsList_wfIn (by simp only [Term.wfIn]; exact ⟨trivial, ht⟩) φ hφ
    | _ => simp [typeConstraints]

  theorem typeConstraintsList_wfIn {ts : List TinyML.Typ} {tl : Term .vallist} {Δ : Signature}
      (htl : tl.wfIn Δ) : ∀ φ ∈ typeConstraints.typeConstraintsList ts tl, φ.wfIn Δ := by
    cases ts with
    | nil => simp [typeConstraints.typeConstraintsList]
    | cons ty rest =>
      simp only [typeConstraints.typeConstraintsList]
      intro φ hφ
      cases List.mem_append.mp hφ with
      | inl h =>
        exact typeConstraints_wfIn (by simp only [Term.wfIn]; exact ⟨trivial, htl⟩) φ h
      | inr h =>
        exact typeConstraintsList_wfIn (by simp only [Term.wfIn]; exact ⟨trivial, htl⟩) φ h
end

mutual
  /-- If `ValHasType v ty` and `t.eval ρ = v`, then all formulas in `typeConstraints ty t` hold. -/
  theorem typeConstraints_hold {ty : TinyML.Typ} {t : Term .value} {ρ : Env}
      {Θ : TinyML.TypeEnv} {v : Runtime.Val} (ht : t.eval ρ = v) (hty : TinyML.ValHasType Θ v ty) :
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

  theorem typeConstraintsList_hold {ts : List TinyML.Typ} {tl : Term .vallist} {ρ : Env}
      {Θ : TinyML.TypeEnv} {vs : List Runtime.Val} (htl : tl.eval ρ = vs) (hty : TinyML.ValsHaveTypes Θ vs ts) :
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
  def Spec.declareArgs (Θ : TinyML.TypeEnv) (σ : FiniteSubst) :
      List (String × TinyML.Typ) → List (TinyML.Typ × Term .value) → VerifM FiniteSubst
  | [], [] => pure σ
  | (name, ty) :: rest, (targ, sarg) :: sargs => do
    if TinyML.Typ.sub Θ targ ty then pure ()
    else VerifM.fatal s!"type mismatch in call to spec"
    let argVar ← VerifM.decl (some name) .value
    let σ' := σ.rename ⟨name, .value⟩ argVar.name
    VerifM.assume (.eq .value (.const (.uninterpreted argVar.name .value)) sarg)
    Spec.declareArgs Θ σ' rest sargs
  | _, _ => VerifM.fatal "wrong number of arguments"

/-- Full call protocol for a spec: declare argument variables, assume they equal the
    compiled argument terms, check argument types, then invoke `PredTrans.call`. -/
def Spec.call (Θ : TinyML.TypeEnv) (σ : FiniteSubst) (s : Spec) (sargs : List (TinyML.Typ × Term .value)) :
    VerifM (TinyML.Typ × Term .value) := do
  let σ' ← Spec.declareArgs Θ σ s.args sargs
  let result ← PredTrans.call σ' s.pred
  VerifM.assumeAll (typeConstraints s.retTy result)
  pure (s.retTy, result)

/-- Declare implementation argument variables: for each `(name, ty)` in `args`,
    declare a fresh variable, assume its type constraints, and rename in `σ`.
    Returns the final substitution and the list of declared argument variables. -/
def Spec.declareImplArgs (σ : FiniteSubst) :
    List (String × TinyML.Typ) → VerifM (FiniteSubst × List FOL.Const)
  | [] => pure (σ, [])
  | (name, ty) :: rest => do
    let argVar ← VerifM.decl (some name) .value
    VerifM.assumeAll (typeConstraints ty (.const (.uninterpreted argVar.name .value)))
    let σ' := σ.rename ⟨name, .value⟩ argVar.name
    let (σ'', vars) ← Spec.declareImplArgs σ' rest
    pure (σ'', argVar :: vars)

/-- Full implementation protocol for a spec: declare argument variables,
    assume type constraints, then invoke `PredTrans.implement`. Dual to `Spec.call`. -/
def Spec.implement (s : Spec) (body : List FOL.Const → VerifM (Term .value)) : VerifM Unit := do
  let (σ, argVars) ← Spec.declareImplArgs FiniteSubst.id s.args
  PredTrans.implement σ s.pred (body argVars)

-- ---------------------------------------------------------------------------
-- SpecMap
-- ---------------------------------------------------------------------------

abbrev SpecMap := Finmap (fun _ : TinyML.Var => Spec)

def SpecMap.satisfiedBy (Θ : TinyML.TypeEnv) (S : SpecMap) (γ : Runtime.Subst) : iProp :=
  iprop(∀ x s, ⌜S.lookup x = some s⌝ -∗ ∃ f, ⌜γ x = some f⌝ ∗ s.isPrecondFor Θ f)

def SpecMap.wfIn (S : SpecMap) (Δ : Signature) : Prop :=
  ∀ f spec, S.lookup f = some spec → spec.wfIn Δ

theorem SpecMap.wfIn_mono {S : SpecMap} {Δ Δ' : Signature}
    (h : S.wfIn Δ) (hsub : Δ.Subset Δ') (hwf : Δ'.wf) :
    S.wfIn Δ' :=
  fun f spec hlookup => Spec.wfIn_mono (h f spec hlookup) hsub hwf

theorem SpecMap.wfIn_erase {S : SpecMap} {x : TinyML.Var} {Δ : Signature}
    (h : S.wfIn Δ) : SpecMap.wfIn (Finmap.erase x S) Δ := by
  intro f spec hlookup
  by_cases hfx : f = x
  · subst hfx; rw [Finmap.lookup_erase] at hlookup; exact absurd hlookup (by simp)
  · rw [Finmap.lookup_erase_ne hfx] at hlookup
    exact h f spec hlookup

/-- Erase multiple keys from a SpecMap. -/
def SpecMap.eraseAll (keys : List String) (S : SpecMap) : SpecMap :=
  keys.foldl (fun acc k => Finmap.erase k acc) S

@[simp] theorem SpecMap.eraseAll_nil (S : SpecMap) : SpecMap.eraseAll [] S = S := rfl

@[simp] theorem SpecMap.eraseAll_cons (k : String) (ks : List String) (S : SpecMap) :
    SpecMap.eraseAll (k :: ks) S = SpecMap.eraseAll ks (Finmap.erase k S) := by
  simp [SpecMap.eraseAll, List.foldl_cons]

theorem SpecMap.eraseAll_lookup_none_of_none {keys : List String} {S : SpecMap} {y : String}
    (h : S.lookup y = none) : (SpecMap.eraseAll keys S).lookup y = none := by
  induction keys generalizing S with
  | nil => exact h
  | cons k ks ih =>
    rw [eraseAll_cons]; apply ih
    by_cases hky : k = y
    · subst hky; simp [Finmap.lookup_erase]
    · rw [Finmap.lookup_erase_ne (Ne.symm hky)]; exact h

theorem SpecMap.eraseAll_lookup_none {keys : List String} {S : SpecMap} {y : String}
    (hy : y ∈ keys) : (SpecMap.eraseAll keys S).lookup y = none := by
  induction keys generalizing S with
  | nil => simp at hy
  | cons k ks ih =>
    rw [eraseAll_cons]; cases List.mem_cons.mp hy with
    | inl heq => subst heq; exact eraseAll_lookup_none_of_none (by simp [Finmap.lookup_erase])
    | inr hmem => exact ih hmem

theorem SpecMap.eraseAll_lookup_of_notin {keys : List String} {y : String}
    (hy : y ∉ keys) (S : SpecMap) :
    (SpecMap.eraseAll keys S).lookup y = S.lookup y := by
  induction keys generalizing S with
  | nil => rfl
  | cons k ks ih =>
    simp at hy
    rw [eraseAll_cons, ih hy.2, Finmap.lookup_erase_ne hy.1]

theorem SpecMap.wfIn_eraseAll {keys : List String} {S : SpecMap} {Δ : Signature}
    (h : S.wfIn Δ) : (SpecMap.eraseAll keys S).wfIn Δ := by
  induction keys generalizing S with
  | nil => exact h
  | cons k ks ih => exact ih (SpecMap.wfIn_erase h)

def SpecMap.insert' (S : SpecMap) (b : Typed.Binder) (spec : Spec) : SpecMap :=
  match b.name with
  | some x => S.insert x spec
  | none => S

def SpecMap.erase' (S : SpecMap) (b : Typed.Binder) : SpecMap :=
  match b.name with
  | some x => S.erase x
  | none => S

theorem SpecMap.satisfiedBy_insert {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst}
    {x : TinyML.Var} {fval : Runtime.Val} {spec : Spec} (hγ : γ x = some fval) :
    S.satisfiedBy Θ γ ∗ spec.isPrecondFor Θ fval ⊢ SpecMap.satisfiedBy Θ (Finmap.insert x spec S) γ := by
  intro y s' hlookup
  by_cases hyx : y = x
  · subst hyx; rw [Finmap.lookup_insert] at hlookup; simp at hlookup; subst hlookup
    exact ⟨fval, hγ, hf⟩
  · rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
    exact hS y s' hlookup

theorem SpecMap.satisfiedBy_insert_update {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst}
    {x : TinyML.Var} {v : Runtime.Val} {spec : Spec} :
    S.satisfiedBy Θ γ ∗ spec.isPrecondFor Θ v ⊢ SpecMap.satisfiedBy Θ (Finmap.insert x spec S) (γ.update x v) := by
  intro y s' hlookup
  by_cases hyx : y = x
  · subst hyx; rw [Finmap.lookup_insert] at hlookup; simp at hlookup; subst hlookup
    exact ⟨v, by simp [Runtime.Subst.update], hf⟩
  · rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
    obtain ⟨f, hγf, hprecond⟩ := hS y s' hlookup
    exact ⟨f, by simp [Runtime.Subst.update, beq_false_of_ne hyx, hγf], hprecond⟩

theorem SpecMap.wfIn_insert {S : SpecMap} {x : TinyML.Var} {spec : Spec} {Δ : Signature}
    (hS : S.wfIn Δ) (hs : spec.wfIn Δ) : SpecMap.wfIn (Finmap.insert x spec S) Δ := by
  intro y s' hlookup
  by_cases hyx : y = x
  · subst hyx; rw [Finmap.lookup_insert] at hlookup; simp at hlookup; subst hlookup; exact hs
  · rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup; exact hS y s' hlookup

theorem SpecMap.satisfiedBy_insert' {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst}
    {b : Typed.Binder} {fval : Runtime.Val} {spec : Spec}
    (hγ : ∀ x ty, b = Typed.Binder.named x ty → γ x = some fval) :
    S.satisfiedBy Θ γ ∗ spec.isPrecondFor Θ fval ⊢ SpecMap.satisfiedBy Θ (S.insert' b spec) γ := by
  cases b with
  | mk name ty =>
    cases name with
    | none => exact hS
    | some x => exact SpecMap.satisfiedBy_insert hS (hγ x ty rfl) hf

theorem SpecMap.satisfiedBy_insert'_update' {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst}
    {b : Typed.Binder} {v : Runtime.Val} {spec : Spec} :
    S.satisfiedBy Θ γ ∗ spec.isPrecondFor Θ v ⊢ SpecMap.satisfiedBy Θ (S.insert' b spec) (Runtime.Subst.update' b.runtime v γ) := by
  cases b with
  | mk name _ =>
    cases name with
    | none => exact hS
    | some _ => exact SpecMap.satisfiedBy_insert_update hS hf

theorem SpecMap.wfIn_insert' {S : SpecMap} {b : Typed.Binder} {spec : Spec} {Δ : Signature}
    (hS : S.wfIn Δ) (hs : spec.wfIn Δ) : SpecMap.wfIn (S.insert' b spec) Δ := by
  cases b with
  | mk name _ =>
    cases name with
    | none => exact hS
    | some x => exact SpecMap.wfIn_insert hS hs

theorem SpecMap.wfIn_erase' {S : SpecMap} {b : Typed.Binder} {Δ : Signature}
    (hS : S.wfIn Δ) : SpecMap.wfIn (S.erase' b) Δ := by
  cases b with
  | mk name _ =>
    cases name with
    | none => exact hS
    | some _ => exact SpecMap.wfIn_erase hS

theorem SpecMap.satisfiedBy_eraseAll_updateAll' {Θ : TinyML.TypeEnv} {keys : List String} {S : SpecMap} {γ : Runtime.Subst}
    {vs : List Runtime.Val} (hlen : keys.length = vs.length) :
    S.satisfiedBy Θ γ ⊢ (SpecMap.eraseAll keys S).satisfiedBy Θ (γ.updateAll' (keys.map Runtime.Binder.named) vs) := by
  intro y s hlookup
  have hy_notin : y ∉ keys := by
    intro hmem
    have := SpecMap.eraseAll_lookup_none hmem (S := S)
    rw [this] at hlookup; exact absurd hlookup (by simp)
  have hγ_eq : (γ.updateAll' (keys.map Runtime.Binder.named) vs) y = γ y := by
    rw [Runtime.Subst.updateAll'_eq _ _ _ _ (by simp; omega)]
    rw [findVal_none_of_not_mem keys vs y (by omega) hy_notin]
  rw [hγ_eq]
  apply hS
  rwa [SpecMap.eraseAll_lookup_of_notin hy_notin] at hlookup

theorem SpecMap.empty_satisfiedBy (γ : Runtime.Subst) :
    ⊢ SpecMap.satisfiedBy Θ (∅ : SpecMap) γ := by
  intro x s h; simp [Finmap.lookup_empty] at h

theorem SpecMap.empty_wfIn (Δ : Signature) :
    SpecMap.wfIn (∅ : SpecMap) Δ := by
  intro f spec h; simp [Finmap.lookup_empty] at h

theorem SpecMap.satisfiedBy_erase {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst} {x : TinyML.Var} {v : Runtime.Val} :
    S.satisfiedBy Θ γ ⊢ SpecMap.satisfiedBy Θ (Finmap.erase x S) (Runtime.Subst.update γ x v) := by
  intro y s hlookup
  by_cases hyx : y = x
  · subst hyx; rw [Finmap.lookup_erase] at hlookup; exact absurd hlookup (by simp)
  · rw [Finmap.lookup_erase_ne hyx] at hlookup
    obtain ⟨fval, hγ, hisPrecond⟩ := h y s hlookup
    exact ⟨fval, by simp [Runtime.Subst.update, hyx, hγ], hisPrecond⟩

theorem SpecMap.satisfiedBy_erase' {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst}
    {b : Typed.Binder} {v : Runtime.Val} :
    S.satisfiedBy Θ γ ⊢ SpecMap.satisfiedBy Θ (S.erase' b) (Runtime.Subst.update' b.runtime v γ) := by
  cases b with
  | mk name _ =>
    cases name with
    | none => exact hS
    | some _ => exact SpecMap.satisfiedBy_erase hS

theorem SpecMap.satisfiedBy_update_of_not_mem {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst}
    {x : TinyML.Var} {v : Runtime.Val} (hx : S.lookup x = none) :
    S.satisfiedBy Θ γ ⊢ S.satisfiedBy Θ (γ.update x v) := by
  intro y s hlookup
  have hyx : y ≠ x := by intro heq; subst heq; rw [hx] at hlookup; exact absurd hlookup (by simp)
  obtain ⟨fval, hγ, hisPrecond⟩ := h y s hlookup
  exact ⟨fval, by simp [Runtime.Subst.update, hyx, hγ], hisPrecond⟩

-- ---------------------------------------------------------------------------
-- Spec correctness
-- ---------------------------------------------------------------------------

/-- `argsEnv` preserves `agreeOn`: if two base envs agree on `Δ`,
    then after applying the same updates, they agree on `argVars args ++ Δ`. -/
theorem Spec.argsEnv_agreeOn {Δ : Signature} {ρ₁ ρ₂ : Env}
    (h : Env.agreeOn Δ ρ₁ ρ₂) :
    ∀ (args : List (String × TinyML.Typ)) (vals : List Runtime.Val),
    args.length ≤ vals.length →
    Env.agreeOn (Δ.declVars (Spec.argVars args))
      (Spec.argsEnv ρ₁ args vals) (Spec.argsEnv ρ₂ args vals) := by
  intro args
  induction args generalizing Δ ρ₁ ρ₂ with
  | nil => intro vals _; simp only [Spec.argVars, List.map, Spec.argsEnv, Signature.declVars]; exact h
  | cons arg rest ih =>
    intro vals hlen
    obtain ⟨name, ty⟩ := arg
    cases vals with
    | nil => simp at hlen
    | cons v vs =>
      simp only [Spec.argsEnv, Spec.argVars, List.map]
      simpa [Signature.declVars] using
        ih (Env.agreeOn_declVar h) vs (by simp [List.length] at hlen ⊢; omega)

/-- Correctness of `declareArgs`: after processing all arguments, the resulting
    substitution is well-formed, types match, and the env agrees with `argsEnv`. -/
theorem Spec.declareArgs_correct (Θ : TinyML.TypeEnv) :
    ∀ (args : List (String × TinyML.Typ)) (sargs : List (TinyML.Typ × Term .value))
      (σ : FiniteSubst) (st : TransState) (ρ : Env)
      (Ψ : FiniteSubst → TransState → Env → Prop),
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
      Env.agreeOn ((Signature.ofVars σ.dom).declVars (Spec.argVars args)) (σ'.subst.eval ρ')
        (Spec.argsEnv (σ.subst.eval ρ) args (sargs.map fun p => p.2.eval ρ)) := by
  intro args
  induction args with
  | nil =>
    intro sargs σ st ρ Ψ hσwf hσdomwf hsargs heval
    cases sargs with
    | nil =>
      simp [Spec.declareArgs] at heval
      have := VerifM.eval_ret heval
      exact ⟨σ, st, ρ, this, hσwf, hσdomwf, rfl, .nil, fun x hx => hx,
        by simp [Spec.argVars, Spec.argsEnv]; exact Env.agreeOn_refl⟩
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
        have hbind := VerifM.eval_bind _ _ _ _ heval
        have hret := VerifM.eval_ret hbind
        have hbind' :
            (VerifM.decl (some name) .value).eval st ρ
              (fun argVar st' ρ' =>
                (do
                  VerifM.assume
                    (Formula.eq Srt.value (Term.const (.uninterpreted argVar.name .value)) sarg)
                  Spec.declareArgs Θ (σ.rename ⟨name, .value⟩ argVar.name) rest sargs_rest).eval
                    st' ρ' Ψ) := by
          simpa using
            (VerifM.eval_bind
              (m := VerifM.decl (some name) .value)
              (k := fun argVar => do
                VerifM.assume
                  (Formula.eq Srt.value (Term.const (.uninterpreted argVar.name .value)) sarg)
                Spec.declareArgs Θ (σ.rename ⟨name, .value⟩ argVar.name) rest sargs_rest)
              (st := st) (ρ := ρ) hret)
        have hdecl := VerifM.eval_decl hbind'
        set argVar := st.freshConst (some name) .value
        have hfresh_decls : argVar.name ∉ st.decls.allNames :=
          fresh_not_mem (addNumbers name) st.decls.allNames (addNumbers_injective _)
        have hfresh_range : argVar.name ∉ σ.range.allNames :=
          fun h => hfresh_decls (Signature.allNames_subset hσwf.2.1 _ h)
        specialize hdecl (sarg.eval ρ)
        set σ' := σ.rename ⟨name, .value⟩ argVar.name
        have hσ'wf : σ'.wf (st.decls.addConst argVar) := by
          simpa [σ'] using
            (FiniteSubst.rename_wf (σ := σ) (v := ⟨name, .value⟩) (name' := argVar.name) hσwf hfresh_range)
        have hsarg_wf : sarg.wfIn st.decls := hsargs (targ, sarg) (List.mem_cons_self ..)
        have heq_wf : (Formula.eq Srt.value (Term.const (.uninterpreted argVar.name .value)) sarg).wfIn
            (st.decls.addConst argVar) := by
          refine ⟨?_, Term.wfIn_mono sarg hsarg_wf (Signature.Subset.subset_addConst _ _) ?_⟩
          · simp only [Term.wfIn, Const.wfIn, Signature.addConst]
            have hwf_add : (st.decls.addConst argVar).wf :=
              Signature.wf_addConst (VerifM.eval.wf heval).namesDisjoint hfresh_decls
            refine ⟨List.Mem.head _, ?_, ?_⟩
            · intro τ' hvar
              exact hfresh_decls (Signature.mem_allNames_of_var hvar)
            · intro τ' hc'
              exact Signature.wf_unique_const hwf_add (List.Mem.head _) hc'
          · exact (TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint
        have heq_holds : (Formula.eq Srt.value (Term.const (.uninterpreted argVar.name .value)) sarg).eval
            (ρ.updateConst .value argVar.name (sarg.eval ρ)) := by
          simp only [Formula.eval, Term.eval, Const.denote]
          simpa [Env.lookupConst, Env.updateConst] using
            (Term.eval_env_agree hsarg_wf (agreeOn_update_fresh_const hfresh_decls))
        have hbind'' := VerifM.eval_bind _ _ _ _ hdecl
        have hassume := VerifM.eval_assume hbind'' heq_wf heq_holds
        set ρ₁ := ρ.updateConst .value argVar.name (sarg.eval ρ)
        have hsargs_rest : ∀ p ∈ sargs_rest, (p : TinyML.Typ × Term .value).2.wfIn
            (st.decls.addConst argVar) := by
          intro p hp
          exact Term.wfIn_mono _ (hsargs p (List.mem_cons_of_mem _ hp))
            (Signature.Subset.subset_addConst _ _)
            ((TransState.freshConst.wf _ (VerifM.eval.wf heval)).namesDisjoint)
        have hsargs_eval : sargs_rest.map (fun p => p.2.eval ρ₁) =
            sargs_rest.map (fun p => p.2.eval ρ) := by
          apply List.map_congr_left
          intro p hp
          exact Term.eval_env_agree
            (hsargs p (List.mem_cons_of_mem _ hp))
            (Env.agreeOn_symm (agreeOn_update_fresh_const hfresh_decls))
        have hσ'domwf : (Signature.ofVars σ'.dom).wf := by
          simpa [σ'] using (FiniteSubst.rename_dom_wf (σ := σ) (v := ⟨name, .value⟩) (name' := argVar.name) hσdomwf)
        obtain ⟨σ'', st'', ρ'', hΨ, hσ''wf, hσ''domwf, howns, hsublist, hdom_sub, hagree⟩ :=
          ih sargs_rest σ' _ ρ₁ Ψ hσ'wf hσ'domwf hsargs_rest hassume
        have hsub_ty' : TinyML.Typ.Sub Θ targ ty := TinyML.Typ.sub_sound hsub_ty
        refine ⟨σ'', st'', ρ'', hΨ, hσ''wf, hσ''domwf,
          howns, .cons hsub_ty' hsublist, ?_, ?_⟩
        · simpa [σ', FiniteSubst.rename, Signature.ofVars, Spec.argVars, Signature.declVars, Signature.declVar]
            using hdom_sub
        · have hag_rename := FiniteSubst.rename_agreeOn_declVar
            (σ := σ) (decls := st.decls) (v := ⟨name, .value⟩) (c := argVar) (ρ := ρ) (u := sarg.eval ρ)
            hσwf hfresh_decls rfl
          have hlen : rest.length ≤ sargs_rest.length := by
            have := TinyML.Typ.SubList.length_eq hsublist
            simp [List.length_map] at this; omega
          have hag_env := Spec.argsEnv_agreeOn hag_rename rest
            (sargs_rest.map fun p => p.2.eval ρ) (by simp [List.length_map]; omega)
          rw [hsargs_eval] at hagree
          simpa [σ', FiniteSubst.rename, Spec.argsEnv, Spec.argVars, Signature.declVars, Signature.declVar] using
            (Env.agreeOn_trans hagree hag_env)
      · simp [hsub_ty] at heval
        have hb := VerifM.eval_bind _ _ _ _ heval
        exact (VerifM.eval_fatal hb).elim

theorem Spec.call_correct (Θ : TinyML.TypeEnv) (s : Spec) (σ : FiniteSubst) (sargs : List (TinyML.Typ × Term .value))
    (st : TransState) (ρ : Env)
    (Ψ : (TinyML.Typ × Term .value) → TransState → Env → Prop)
    (Φ : Runtime.Val → iProp) (R : iProp) :
    s.pred.wfIn ((Signature.ofVars σ.dom).declVars (Spec.argVars s.args)) →
    (Signature.ofVars σ.dom).wf →
    σ.wf st.decls →
    (∀ p ∈ sargs, (p : TinyML.Typ × Term .value).2.wfIn st.decls) →
    VerifM.eval (Spec.call Θ σ s sargs) st ρ Ψ →
    (∀ v st' ρ' t, Ψ (s.retTy, t) st' ρ' → t.wfIn st'.decls → t.eval ρ' = v →
      TinyML.ValHasType Θ v s.retTy → st'.owns.interp ρ' ∗ R ⊢ Φ v) →
    @TinyML.Typ.SubList Θ (sargs.map Prod.fst) (s.args.map Prod.snd) ∧
    (st.owns.interp ρ ∗ R ⊢ PredTrans.apply (fun r => ⌜TinyML.ValHasType Θ r s.retTy⌝ -∗ Φ r) s.pred
      (Spec.argsEnv (σ.subst.eval ρ) s.args (sargs.map fun p => p.2.eval ρ))) := by
  intro hwf hσdomwf hσwf hsargs heval hΨ
  simp only [Spec.call] at heval
  have hb := VerifM.eval_bind _ _ _ _ heval
  have hb_grow := VerifM.eval.decls_grow ρ hb
  obtain ⟨σ', st', ρ', hΨ', hσ'wf, hσ'domwf, howns, hsublist, hdom_sub, hagree⟩ :=
    Spec.declareArgs_correct Θ s.args sargs σ st ρ _ hσwf hσdomwf hsargs hb_grow
  obtain ⟨hdsub, hragree, hΨ'⟩ := hΨ'
  constructor
  · exact hsublist
  · have hb2 := VerifM.eval_bind _ _ _ _ hΨ'
    have hwf'' : s.pred.wfIn (Signature.ofVars σ'.dom) := by
      exact PredTrans.wfIn_mono (Δ := (Signature.ofVars σ.dom).declVars (Spec.argVars s.args))
        (Δ' := Signature.ofVars σ'.dom) hwf
        ⟨hdom_sub,
          by intro c hc; simp at hc,
          by intro u hu; simp at hu,
          by intro b hb; simp at hb⟩
        hσ'domwf
    have hcall := PredTrans.call_correct s.pred σ' st' ρ'
      _ (fun r => ⌜TinyML.ValHasType Θ r s.retTy⌝ -∗ Φ r) R
      hwf'' hσ'domwf hσ'wf hb2
      (fun v st'' ρ'' t hΨ'' htwf hteval => by
        apply wand_intro
        iintro H
        icases H with ⟨⟨Howns, HR⟩, %hty⟩
        have hbind := VerifM.eval_bind _ _ _ _ hΨ''
        have hassumeAll :
            ∃ st₃, st₃.decls = st''.decls ∧ st₃.owns = st''.owns ∧
              VerifM.eval (Pure.pure (s.retTy, t)) st₃ ρ'' Ψ :=
          VerifM.eval_assumeAll hbind
          (fun φ hφ => typeConstraints_wfIn htwf φ hφ)
          (fun φ hφ => typeConstraints_hold hteval hty φ hφ)
        rcases hassumeAll with ⟨st₃, hst₃_decls, hrest⟩
        have hst₃_owns : st₃.owns = st''.owns := hrest.1
        have heval_pure : VerifM.eval (Pure.pure (s.retTy, t)) st₃ ρ'' Ψ := hrest.2
        have hret := VerifM.eval_ret heval_pure
        iapply (hΨ v st₃ ρ'' t hret (hst₃_decls ▸ htwf) hteval hty)
        isplitl [Howns]
        · simpa [hst₃_owns] using Howns
        · iexact HR)
    have hcall' : st.owns.interp ρ' ∗ R ⊢
        PredTrans.apply (fun r => ⌜TinyML.ValHasType Θ r s.retTy⌝ -∗ Φ r) s.pred
          (σ'.subst.eval ρ') := by
      simpa [howns] using hcall
    exact (sep_mono_l (SpatialContext.interp_env_agree (VerifM.eval.wf heval).ownsWf hragree).1).trans <|
      hcall'.trans <| PredTrans.apply_env_agree hwf hagree

/-- Correctness of `declareImplArgs`: after processing all arguments, the resulting
    substitution is well-formed, all argVars are in decls with sort `.value`,
    and the env agrees with `argsEnv`. -/
theorem Spec.declareImplArgs_correct (Θ : TinyML.TypeEnv) :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val)
      (σ : FiniteSubst) (st : TransState) (ρ : Env)
      (Ψ : (FiniteSubst × List FOL.Const) → TransState → Env → Prop),
    σ.wf st.decls →
    (Signature.ofVars σ.dom).wf →
    TinyML.ValsHaveTypes Θ vs (args.map Prod.snd) →
    VerifM.eval (Spec.declareImplArgs σ args) st ρ Ψ →
    ∃ σ' argVars st' ρ', Ψ (σ', argVars) st' ρ' ∧
      σ'.wf st'.decls ∧
      (Signature.ofVars σ'.dom).wf ∧
      st.decls.Subset st'.decls ∧
      Env.agreeOn st.decls ρ ρ' ∧
      st'.owns = st.owns ∧
      (((Signature.ofVars σ.dom).declVars (Spec.argVars args)).vars ⊆ σ'.dom) ∧
      Env.agreeOn ((Signature.ofVars σ.dom).declVars (Spec.argVars args)) (σ'.subst.eval ρ')
        (Spec.argsEnv (σ.subst.eval ρ) args vs) ∧
      (∀ v ∈ argVars, v ∈ st'.decls.consts) ∧
      (∀ v ∈ argVars, v.sort = .value) ∧
      Terms.Eval ρ' (argVars.map (fun av => .const (.uninterpreted av.name .value))) vs := by
  intro args
  induction args with
  | nil =>
    intro vs σ st ρ Ψ hσwf hσdomwf hvs heval
    cases hvs with
    | nil =>
      simp [Spec.declareImplArgs] at heval
      have := VerifM.eval_ret heval
      exact ⟨σ, [], st, ρ, this, hσwf, hσdomwf,
        Signature.Subset.refl _, Env.agreeOn_refl, rfl, fun x hx => hx,
        by simp [Spec.argVars, Spec.argsEnv]; exact Env.agreeOn_refl,
        nofun,
        nofun,
        .nil⟩
  | cons arg rest ih =>
    intro vs σ st ρ Ψ hσwf hσdomwf hvs heval
    obtain ⟨name, ty⟩ := arg
    cases hvs with
    | cons hv hvs_rest =>
      rename_i v vs'
      simp only [Spec.declareImplArgs] at heval
      have hb := VerifM.eval_bind _ _ _ _ heval
      have hdecl := VerifM.eval_decl hb
      set argVar := st.freshConst (some name) .value
      specialize hdecl v
      have hfresh_decls : argVar.name ∉ st.decls.allNames :=
        fresh_not_mem (addNumbers name) st.decls.allNames (addNumbers_injective _)
      have hfresh_range : argVar.name ∉ σ.range.allNames :=
        fun h => hfresh_decls (Signature.allNames_subset hσwf.2.1 _ h)
      set st₁ : TransState := { st with decls := st.decls.addConst argVar }
      set ρ₁ := ρ.updateConst .value argVar.name v
      -- Peel off assumeAll
      have hwfst₁ : st₁.decls.wf := (VerifM.eval.wf hdecl).namesDisjoint
      have hvar_wf : (Term.const (.uninterpreted argVar.name .value)).wfIn st₁.decls := by
        simp only [Term.wfIn, Const.wfIn, st₁, Signature.addConst]
        refine ⟨List.Mem.head _, ?_, ?_⟩
        · intro τ' hvar
          exact hfresh_decls (Signature.mem_allNames_of_var hvar)
        · intro τ' hc'
          exact Signature.wf_unique_const hwfst₁ (List.Mem.head _) hc'
      have hvar_eval : (Term.const (.uninterpreted argVar.name .value)).eval ρ₁ = v := by
        simp [ρ₁, Term.eval, Const.denote, Env.updateConst]
      have hassume_bind := VerifM.eval_bind _ _ _ _ hdecl
      set σ' := σ.rename ⟨name, .value⟩ argVar.name
      have hassumeAll :
          ∃ st₂, st₂.decls = st₁.decls ∧ st₂.owns = st₁.owns ∧
            VerifM.eval
              (do
                let (σ'', vars) ← Spec.declareImplArgs σ' rest
                pure (σ'', argVar :: vars)) st₂ ρ₁ Ψ :=
        VerifM.eval_assumeAll hassume_bind
        (fun φ hφ => typeConstraints_wfIn hvar_wf φ hφ)
        (fun φ hφ => typeConstraints_hold hvar_eval hv φ hφ)
      rcases hassumeAll with ⟨st₂, hst₂_decls, hrest⟩
      have hst₂_owns : st₂.owns = st₁.owns := hrest.1
      have hdecl₂ : VerifM.eval
          (do
            let (σ'', vars) ← Spec.declareImplArgs σ' rest
            pure (σ'', argVar :: vars)) st₂ ρ₁ Ψ := hrest.2
      have hσ'wf : σ'.wf st₁.decls := by
        simpa [st₁, σ'] using
          (FiniteSubst.rename_wf (σ := σ) (v := ⟨name, .value⟩) (name' := argVar.name) hσwf hfresh_range)
      have hσ'wf₂ : σ'.wf st₂.decls := hst₂_decls ▸ hσ'wf
      have hst_st₂ : st.decls.Subset st₂.decls := by
        rw [hst₂_decls]; exact Signature.Subset.subset_addConst _ _
      have hσ'domwf : (Signature.ofVars σ'.dom).wf := by
        simpa [σ'] using (FiniteSubst.rename_dom_wf (σ := σ) (v := ⟨name, .value⟩) (name' := argVar.name) hσdomwf)
      have hbind₂ := VerifM.eval_bind _ _ _ _ hdecl₂
      have hbind₂' : VerifM.eval (Spec.declareImplArgs σ' rest) st₂ ρ₁
          (fun p st' ρ' => Ψ (p.1, argVar :: p.2) st' ρ') := by
        apply VerifM.eval.mono hbind₂
        intro p st' ρ' hp
        exact VerifM.eval_ret hp
      have hih :
          ∃ σ'' argVars' st' ρ', Ψ (σ'', argVar :: argVars') st' ρ' ∧
            σ''.wf st'.decls ∧
            (Signature.ofVars σ''.dom).wf ∧
            st₂.decls.Subset st'.decls ∧
            Env.agreeOn st₂.decls ρ₁ ρ' ∧
            st'.owns = st₂.owns ∧
            (((Signature.ofVars σ'.dom).declVars (Spec.argVars rest)).vars ⊆ σ''.dom) ∧
            Env.agreeOn ((Signature.ofVars σ'.dom).declVars (Spec.argVars rest)) (σ''.subst.eval ρ')
              (Spec.argsEnv (σ'.subst.eval ρ₁) rest vs') ∧
            (∀ v ∈ argVars', v ∈ st'.decls.consts) ∧
            (∀ v ∈ argVars', v.sort = .value) ∧
            Terms.Eval ρ' (argVars'.map (fun av => .const (.uninterpreted av.name .value))) vs' :=
        ih vs' σ' st₂ ρ₁
          (fun p st' ρ' => Ψ (p.1, argVar :: p.2) st' ρ')
          hσ'wf₂ hσ'domwf hvs_rest hbind₂'
      rcases hih with ⟨σ'', argVars', st', ρ', hΨ, hrest⟩
      rcases hrest with ⟨hσ''wf, hrest⟩
      rcases hrest with ⟨hσ''domwf, hrest⟩
      rcases hrest with ⟨hdsub', hrest⟩
      rcases hrest with ⟨hragree', hrest⟩
      rcases hrest with ⟨howns, hrest⟩
      rcases hrest with ⟨hdom_sub, hrest⟩
      rcases hrest with ⟨hagree, hrest⟩
      rcases hrest with ⟨hmem_decls, hrest⟩
      rcases hrest with ⟨hsorts, hlookups⟩
      refine ⟨σ'', argVar :: argVars', st', ρ', hΨ, hσ''wf, hσ''domwf,
        Signature.Subset.trans hst_st₂ hdsub', ?_⟩
      have hst_st₂_sig : st.decls.Subset st₂.decls :=
        hst₂_decls ▸ Signature.Subset.subset_addConst st.decls argVar
      have hragree_final : Env.agreeOn st.decls ρ ρ' :=
        Env.agreeOn_trans (agreeOn_update_fresh_const hfresh_decls)
          (Env.agreeOn_mono hst_st₂_sig hragree')
      have howns_final : st'.owns = st.owns := by
        calc
          st'.owns = st₂.owns := howns
          _ = st₁.owns := hst₂_owns
          _ = st.owns := rfl
      have hdom_sub_final :
          (((Signature.ofVars σ.dom).declVars (Spec.argVars ((name, ty) :: rest))).vars ⊆ σ''.dom) := by
        simpa [σ', FiniteSubst.rename, Signature.ofVars, Spec.argVars, Signature.declVars, Signature.declVar]
          using hdom_sub
      have hag_rename := FiniteSubst.rename_agreeOn_declVar
          (σ := σ) (decls := st.decls) (v := ⟨name, .value⟩) (c := argVar) (ρ := ρ) (u := v)
          hσwf hfresh_decls rfl
      have hag_env := Spec.argsEnv_agreeOn hag_rename rest vs' (by
          have := hvs_rest.length_eq
          simp [List.length_map] at this; omega)
      have hagree_final :
          Env.agreeOn ((Signature.ofVars σ.dom).declVars (Spec.argVars ((name, ty) :: rest))) (σ''.subst.eval ρ')
            (Spec.argsEnv (σ.subst.eval ρ) ((name, ty) :: rest) (v :: vs')) := by
        simpa [σ', FiniteSubst.rename, Spec.argsEnv, Spec.argVars, Signature.declVars, Signature.declVar] using
          (Env.agreeOn_trans hagree hag_env)
      have hmem_final : ∀ w ∈ argVar :: argVars', w ∈ st'.decls.consts := by
        intro w hw
        cases List.mem_cons.mp hw with
        | inl h => subst h; exact hdsub'.consts argVar (hst₂_decls ▸ List.mem_cons_self ..)
        | inr h => exact hmem_decls w h
      have hsorts_final : ∀ w ∈ argVar :: argVars', w.sort = .value := by
        intro w hw
        cases List.mem_cons.mp hw with
        | inl h => subst h; rfl
        | inr h => exact hsorts w h
      have hlookups_final :
          Terms.Eval ρ' ((argVar :: argVars').map (fun av => .const (.uninterpreted av.name .value))) (v :: vs') := by
        constructor
        · have h1 := hragree'.2.1 argVar (hst₂_decls ▸ List.mem_cons_self ..)
          have h1' : Term.eval ρ' (Term.const (.uninterpreted argVar.name .value)) =
              Term.eval ρ₁ (Term.const (.uninterpreted argVar.name .value)) := by
            simpa [Term.eval, Const.denote, Env.lookupConst] using h1.symm
          exact h1'.trans hvar_eval
        · exact hlookups
      exact ⟨hragree_final, howns_final, hdom_sub_final, hagree_final, hmem_final, hsorts_final, hlookups_final⟩

theorem Spec.implement_correct (Θ : TinyML.TypeEnv) (s : Spec) (body : List FOL.Const → VerifM (Term .value))
    (st : TransState) (ρ : Env) (vs : List Runtime.Val) (Φ : Runtime.Val → iProp) (R : iProp) :
    s.wfIn Signature.empty →
    TinyML.ValsHaveTypes Θ vs (s.args.map Prod.snd) →
    VerifM.eval (Spec.implement s body) st ρ (fun _ _ _ => True) →
    (∀ (argVars : List FOL.Const) (st' : TransState) (ρ' : Env) (Q : iProp),
      (∀ v ∈ argVars, v ∈ st'.decls.consts) →
      (∀ v ∈ argVars, v.sort = .value) →
      List.Forall₂ (fun av val => ρ'.consts .value av.name = val) argVars vs →
      VerifM.eval (body argVars) st' ρ'
        (fun result st'' ρ'' =>
          ∀ (S : iProp), result.wfIn st''.decls →
            st''.owns.interp ρ'' ∗ Q ∗ ((⌜TinyML.ValHasType Θ (result.eval ρ'') s.retTy⌝ -∗ Φ (result.eval ρ'')) -∗ S) ⊢ S) →
      st'.owns.interp ρ' ∗ Q ⊢ R) →
    st.owns.interp ρ ∗ PredTrans.apply (fun r => ⌜TinyML.ValHasType Θ r s.retTy⌝ -∗ Φ r) s.pred
      (Spec.argsEnv Env.empty s.args vs) ⊢ R := by
  intro hswf hvs heval hR
  simp only [Spec.implement] at heval
  have hb := VerifM.eval_bind _ _ _ _ heval
  obtain ⟨σ', argVars, st', ρ', hΨ, hσ'wf, hσ'domwf, hdsub, hragree, howns, hdom_sub, hagree,
    hmem_decls, hsorts, hlookups⟩ :=
    Spec.declareImplArgs_correct Θ s.args vs FiniteSubst.id st ρ _ (FiniteSubst.id_wf st.decls)
      (by simpa [Signature.ofVars] using Signature.wf_empty) hvs hb
  -- Transport apply from argsEnv Env.empty to σ'.subst.eval ρ'
  have hag_empty : Env.agreeOn ((Signature.ofVars FiniteSubst.id.dom).declVars (Spec.argVars s.args))
      (Spec.argsEnv Env.empty s.args vs)
      (Spec.argsEnv (FiniteSubst.id.subst.eval ρ) s.args vs) :=
    Spec.argsEnv_agreeOn (Δ := Signature.empty) (ρ₁ := Env.empty) (ρ₂ := FiniteSubst.id.subst.eval ρ)
      ⟨nofun, nofun, nofun, nofun⟩ s.args vs
      (by have := hvs.length_eq; simp [List.length_map] at this; omega)
  refine (show st.owns.interp ρ ∗
      PredTrans.apply (fun r => ⌜TinyML.ValHasType Θ r s.retTy⌝ -∗ Φ r) s.pred
        (Spec.argsEnv Env.empty s.args vs) ⊢
      st'.owns.interp ρ' ∗
        PredTrans.apply (fun r => ⌜TinyML.ValHasType Θ r s.retTy⌝ -∗ Φ r) s.pred
          (σ'.subst.eval ρ') from by
      iintro H
      icases H with ⟨Howns, Happ⟩
      isplitr [Happ]
      · iapply (show st.owns.interp ρ' ⊢ st'.owns.interp ρ' by simpa [howns])
        iapply (SpatialContext.interp_env_agree (VerifM.eval.wf heval).ownsWf hragree).1
        iexact Howns
      · iapply (PredTrans.apply_env_agree hswf (Env.agreeOn_trans hag_empty (Env.agreeOn_symm hagree)))
        iexact Happ).trans
    (PredTrans.implement_correct s.pred σ' (body argVars) st' ρ'
      (fun r => ⌜TinyML.ValHasType Θ r s.retTy⌝ -∗ Φ r) R
      (PredTrans.wfIn_mono hswf
        ⟨hdom_sub,
          by
            intro c hc
            change c ∈ ((Signature.ofVars ([] : List Var)).declVars (Spec.argVars s.args)).consts at hc
            simp at hc,
          by
            intro u hu
            change u ∈ ((Signature.ofVars ([] : List Var)).declVars (Spec.argVars s.args)).unary at hu
            simp at hu,
          by
            intro b hb
            change b ∈ ((Signature.ofVars ([] : List Var)).declVars (Spec.argVars s.args)).binary at hb
            simp at hb⟩
        hσ'domwf) hσ'domwf hσ'wf hΨ
        (fun st'' ρ'' Q hdsub' hragree' hbody_eval => by
          apply hR argVars st'' ρ'' Q
          · intro v hv
            exact hdsub'.consts v (hmem_decls v hv)
          · exact hsorts
          · apply Terms.Eval.lookup_const
            apply Terms.Eval.env_agree (ρ := ρ')
            · intro t ht
              obtain ⟨av, hav, rfl⟩ := List.mem_map.mp ht
              simp only [Term.wfIn, Const.wfIn]
              cases av with
              | mk name sort =>
                have hsort : sort = .value := hsorts ⟨name, sort⟩ hav
                subst hsort
                have hwfst' : st'.decls.wf := (VerifM.eval.wf hΨ).namesDisjoint
                refine ⟨hmem_decls ⟨name, .value⟩ hav, ?_, ?_⟩
                · intro τ' hvar
                  exact Signature.wf_no_var_of_const hwfst' (hmem_decls ⟨name, .value⟩ hav) hvar
                · intro τ' hc'
                  exact Signature.wf_unique_const hwfst' (hmem_decls ⟨name, .value⟩ hav) hc'
            · exact hragree'
            · exact hlookups
          · exact hbody_eval))

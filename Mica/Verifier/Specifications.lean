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

/-- A complete specification for a single-argument function, pairing the predicate
    transformer with the argument and return types from the function annotation.
    Currently, the types are used as a guard on `isPrecondFor` (the caller must provide
    a well-typed argument, and gets to assume a well-typed return value). In the future,
    the type constraints could also be integrated directly into the predicate transformer. -/
structure Spec where
  argName : String
  argTy   : TinyML.Type_
  retTy   : TinyML.Type_
  pred    : PredTrans

-- ---------------------------------------------------------------------------
-- Printers
-- ---------------------------------------------------------------------------

def SpecPredicate.toStringHum (s : SpecPredicate) : String :=
  Pred.toStringHum (Assertion.toStringHum (Pred.toStringHum (Assertion.toStringHum (fun () => "()")))) s

-- ---------------------------------------------------------------------------
-- Well-formedness
-- ---------------------------------------------------------------------------

def Spec.isPrecondFor (f : TinyML.Val) (s : Spec) : Prop :=
  ∀ (v : TinyML.Val), TinyML.ValHasType v s.argTy →
    ∀ (Φ : TinyML.Val → Prop),
      PredTrans.apply (fun r => TinyML.ValHasType r s.retTy → Φ r) s.pred (Env.empty.update .value s.argName v) →
      wp (TinyML.Expr.app (.val f) (.val v)) Φ

/-- A spec is well-formed when its predicate transformer is well-formed in the
    context extended with the argument variable. -/
def Spec.wfIn (spec : Spec) (decls : List Var) : Prop :=
  PredTrans.wfIn (⟨spec.argName, .value⟩ :: decls) spec.pred

def Spec.checkWf (spec : Spec) (decls : List Var) : Except String Unit :=
  PredTrans.checkWf (⟨spec.argName, .value⟩ :: decls) spec.pred

theorem Spec.checkWf_ok {spec : Spec} {decls : List Var}
    (h : spec.checkWf decls = .ok ()) : spec.wfIn decls :=
  PredTrans.checkWf_ok h

theorem Spec.wfIn_mono {spec : Spec} {decls decls' : List Var}
    (h : spec.wfIn decls) (hsub : decls ⊆ decls') : spec.wfIn decls' :=
  PredTrans.wfIn_mono h (List.cons_subset_cons _ hsub)

-- ---------------------------------------------------------------------------
-- Spec verifier operations
-- ---------------------------------------------------------------------------

/-- Full call protocol for a spec: declare the argument variable, assume it equals the
    compiled argument term, check the argument type, then invoke `PredTrans.call`. -/
def Spec.call (σ : FiniteSubst) (s : Spec) (sarg : Term .value) (targ : TinyML.Type_) : VerifM (TinyML.Type_ × Term .value) := do
  if targ.sub s.argTy then pure ()
  else VerifM.fatal s!"type mismatch in call to spec"
  let argVar ← VerifM.decl (some s.argName) .value
  let σ' := σ.rename ⟨s.argName, .value⟩ argVar.name
  VerifM.assume (.eq .value (.var .value argVar.name) sarg)
  let result ← PredTrans.call σ' s.pred
  pure (s.retTy, result)

/-- Full implementation protocol for a spec: declare the argument variable,
    then invoke `PredTrans.implement`. Dual to `Spec.call`. -/
def Spec.implement (s : Spec) (body : Var → VerifM (Term .value)) : VerifM Unit := do
  let argVar ← VerifM.decl (some s.argName) .value
  let σ₀ := FiniteSubst.id.rename ⟨s.argName, .value⟩ argVar.name
  PredTrans.implement σ₀ s.pred (body argVar)

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

theorem Spec.call_correct (s : Spec) (σ : FiniteSubst) (sarg : Term .value) (targ : TinyML.Type_)
    (st : TransState) (ρ : Env)
    (Ψ : (TinyML.Type_ × Term .value) → TransState → Env → Prop)
    (Φ : TinyML.Val → Prop) :
    s.pred.wfIn (⟨s.argName, .value⟩ :: σ.dom) →
    σ.wf st.decls →
    sarg.wfIn st.decls →
    VerifM.eval (Spec.call σ s sarg targ) st ρ Ψ →
    (∀ v st' ρ' t, Ψ (s.retTy, t) st' ρ' → t.wfIn st'.decls → t.eval ρ' = v → Φ v) →
    TinyML.Type_.Sub targ s.argTy ∧
    PredTrans.apply Φ s.pred ((σ.subst.eval ρ).update .value s.argName (sarg.eval ρ)) := by
  intro hwf hσwf hsarg heval hΨ
  simp only [Spec.call] at heval
  -- Split on type check; since eval succeeds, it must be true
  by_cases hsub_ty : targ.sub s.argTy = true
  · simp [hsub_ty] at heval
    constructor
    · exact TinyML.Type_.sub_iff.mp hsub_ty
    -- Decompose VerifM.decl for the argument variable
    have hb1 := VerifM.eval_bind _ _ _ _ heval
    have hb1 := VerifM.eval_ret hb1
    have hb2 := VerifM.eval_bind _ _ _ _ hb1
    have hdecl := VerifM.eval_decl hb2
    set argVar := st.freshVar (some s.argName) .value
    have hfresh_decls : argVar.name ∉ st.decls.map Var.name :=
      fresh_not_mem (addNumbers s.argName) (st.decls.map Var.name) (addNumbers_injective _)
    have hfresh_range : ⟨argVar.name, Srt.value⟩ ∉ σ.range := by
      intro hmem; exact hfresh_decls (List.mem_map.mpr ⟨⟨argVar.name, .value⟩, hσwf.2 hmem, rfl⟩)
    specialize hdecl (sarg.eval ρ)
    have hb3 := VerifM.eval_bind _ _ _ _ hdecl
    set σ' := σ.rename ⟨s.argName, .value⟩ argVar.name
    have hσ'wf : σ'.wf (argVar :: st.decls) := FiniteSubst.rename_wf hσwf hfresh_range
    have heq_wf : (Formula.eq Srt.value (Term.var .value argVar.name) sarg).wfIn
        (argVar :: st.decls) := by
      intro w hw
      simp only [Formula.freeVars, Term.freeVars] at hw
      cases hw with
      | head => exact .head _
      | tail _ hw => exact .tail _ (hsarg w hw)
    have heq_holds : (Formula.eq Srt.value (Term.var .value argVar.name) sarg).eval
        (ρ.update .value argVar.name (sarg.eval ρ)) := by
      simp only [Formula.eval, Term.eval, Env.lookup_update_same]
      exact Term.eval_env_agree hsarg (agreeOn_update_fresh hfresh_decls)
    have hassume := VerifM.eval_assume hb3 heq_wf heq_holds
    have hb4 := VerifM.eval_bind _ _ _ _ hassume
    -- Apply PredTrans.call_correct with σ'
    have hcall := PredTrans.call_correct s.pred σ'
      { st with decls := argVar :: st.decls,
                asserts := Formula.eq Srt.value (Term.var .value argVar.name) sarg :: st.asserts }
      (ρ.update .value argVar.name (sarg.eval ρ)) _ Φ hwf hσ'wf hb4
      (fun v st' ρ' t hΨ' htwf hteval => by
        have hret := VerifM.eval_ret hΨ'
        exact hΨ v st' ρ' t hret htwf hteval)
    -- Transport from σ'.subst.eval ρ' to (σ.subst.eval ρ).update .value s.argName (sarg.eval ρ)
    exact PredTrans.apply_env_agree hwf
      (FiniteSubst.rename_agreeOn hσwf.1 hfresh_range) hcall
  · simp [hsub_ty] at heval
    have hb := VerifM.eval_bind _ _ _ _ heval
    exact (VerifM.eval_fatal hb).elim

theorem Spec.implement_correct (s : Spec) (body : Var → VerifM (Term .value))
    (st : TransState) (ρ : Env) (v : TinyML.Val) (Φ : TinyML.Val → Prop) (R : Prop) :
    s.wfIn [] →
    VerifM.eval (Spec.implement s body) st ρ (fun _ _ _ => True) →
    PredTrans.apply Φ s.pred (Env.empty.update .value s.argName v) →
    (∀ argVar st' ρ',
      argVar ∈ st'.decls →
      argVar.sort = .value →
      ρ'.lookup .value argVar.name = v →
      VerifM.eval (body argVar) st' ρ'
        (fun result st'' ρ'' => result.wfIn st''.decls → Φ (result.eval ρ'')) → R) →
    R := by
  intro hswf heval happly hR
  simp only [Spec.implement] at heval
  have hb := VerifM.eval_bind _ _ _ _ heval
  have hdecl := VerifM.eval_decl hb
  set argVar := st.freshVar (some s.argName) .value
  specialize hdecl v
  -- hdecl : PredTrans.implement σ₀ s.pred (body argVar) eval at updated state
  set σ₀ := FiniteSubst.id.rename ⟨s.argName, .value⟩ argVar.name
  set st₁ : TransState := { st with decls := argVar :: st.decls }
  set ρ₁ := ρ.update .value argVar.name v
  -- σ₀.wf st₁.decls
  have hfresh_decls : argVar.name ∉ st.decls.map Var.name :=
    fresh_not_mem (addNumbers s.argName) (st.decls.map Var.name) (addNumbers_injective _)
  have hfresh_range : ⟨argVar.name, Srt.value⟩ ∉ FiniteSubst.id.range := by
    simp [FiniteSubst.id]
  have hσ₀wf : σ₀.wf st₁.decls := FiniteSubst.rename_wf (FiniteSubst.id_wf st.decls) hfresh_range
  -- Transport apply from Env.empty.update to σ₀.subst.eval ρ₁
  have hag_rename := @FiniteSubst.rename_agreeOn FiniteSubst.id ⟨s.argName, .value⟩ argVar.name
    ρ v (FiniteSubst.id_wf st.decls).1 hfresh_range
  -- hag_rename : agreeOn [⟨s.argName, .value⟩] (σ₀.subst.eval ρ₁) ((Subst.id.eval ρ).update .value s.argName v)
  have hag_empty : Env.agreeOn [⟨s.argName, .value⟩]
      (Env.empty.update .value s.argName v)
      ((Subst.id.eval ρ).update .value s.argName v) := by
    intro w hw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
    subst hw
    simp [Env.lookup_update_same]
  have happly' : PredTrans.apply Φ s.pred (σ₀.subst.eval ρ₁) :=
    PredTrans.apply_env_agree hswf (Env.agreeOn_trans hag_empty (Env.agreeOn_symm hag_rename)) happly
  -- Apply PredTrans.implement_correct
  apply PredTrans.implement_correct s.pred σ₀ (body argVar) st₁ ρ₁ Φ R hswf hσ₀wf hdecl happly'
  -- Callback: given body eval with decls/agree info, derive R
  intro st' ρ' hdsub hragree hbody_eval
  apply hR argVar st' ρ'
  · exact hdsub (List.mem_cons_self ..)
  · rfl
  · have := hragree ⟨argVar.name, .value⟩ (List.mem_cons_self ..)
    simp [ρ₁, Env.lookup_update_same] at this
    exact this.symm
  · exact hbody_eval

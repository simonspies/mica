import Mica.TinyML.Expr
import Mica.TinyML.Typing
import Mica.TinyML.OpSem
import Mica.FOL.Printing
import Mica.FOL.Subst
import Mica.Base.Fresh
import Mica.Base.Except
import Mathlib.Data.Finmap

/-! ### Bindings -/

abbrev Bindings := List (TinyML.Var × Var)

-- Every variable in Bindings is now declared at sort `.value`.
def Bindings.agreeOnLinked (B : Bindings) (ρ : Env) (γ : TinyML.Subst) :=
  ∀ x x', B.lookup x = some x' →
    x'.sort = .value ∧ γ x = .some (ρ.lookup .value x'.name)

def Bindings.wf (B : Bindings) (decls : VarCtx) : Prop :=
  ∀ p ∈ B, p.2 ∈ decls

theorem Bindings.agreeOnLinked_env_agree {B : Bindings} {decls : VarCtx} {ρ ρ' : Env} {γ : TinyML.Subst}
    (hagr : B.agreeOnLinked ρ γ) (henv : Env.agreeOn decls ρ ρ')
    (hwf : B.wf decls) : B.agreeOnLinked ρ' γ := by
  intro x x' hmem
  obtain ⟨hsort, hγ⟩ := hagr x x' hmem
  obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hmem
  have hmem' : (x, x') ∈ B := by rw [heq]; simp
  have hdecl := hwf _ hmem'
  have henv' := henv x' hdecl
  rw [hsort] at henv'
  exact ⟨hsort, hγ.trans (congrArg some henv')⟩

theorem Bindings.wf_cons {B : Bindings} {decls : VarCtx} {x : TinyML.Var} {v : Var}
    (hbwf : B.wf decls) :
    Bindings.wf ((x, v) :: B) (v :: decls) := by
  intro p hp
  simp [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact List.Mem.head _
  · exact List.Mem.tail _ (hbwf p hp)

/-- The substitution `γ` maps every binding to a value well-typed by `Γ`. -/
def Bindings.typedSubst (B : Bindings) (Γ : TinyML.TyCtx) (γ : TinyML.Subst) : Prop :=
  ∀ x x' t, B.lookup x = some x' → Γ x = some t → ∃ v, γ x = some v ∧ TinyML.ValHasType v t

theorem Bindings.typedSubst_cons {B : Bindings} {Γ : TinyML.TyCtx} {γ : TinyML.Subst}
    {x : TinyML.Var} {v : Var} {te : TinyML.Type_} {w : TinyML.Val}
    (hts  : B.typedSubst Γ γ)
    (hval : TinyML.ValHasType w te) :
    Bindings.typedSubst ((x, v) :: B) (Γ.extend x te) (TinyML.Subst.update γ x w) := by
  intro y y' t hmem hΓ
  by_cases hyx : y == x
  · -- head case: y = x
    simp [List.lookup, hyx] at hmem; subst hmem
    simp [TinyML.TyCtx.extend, hyx] at hΓ; subst hΓ
    exact ⟨w, by simp [TinyML.Subst.update, hyx], hval⟩
  · -- tail case: y ≠ x
    simp [List.lookup, hyx] at hmem
    have hΓ' : Γ y = some t := by simp [TinyML.TyCtx.extend, hyx] at hΓ; exact hΓ
    obtain ⟨w', hw', hwt'⟩ := hts y y' t hmem hΓ'
    exact ⟨w', by simp [TinyML.Subst.update, hyx, hw'], hwt'⟩

theorem Bindings.agreeOnLinked_cons {B : Bindings} {ρ ρ' : Env} {γ : TinyML.Subst}
    {x : TinyML.Var} {v : Var}
    (hagree : B.agreeOnLinked ρ γ)
    (hρ_agree : Env.agreeOn (B.map Prod.snd) ρ' ρ)
    (hvty : v.sort = .value) :
    Bindings.agreeOnLinked ((x, v) :: B) ρ' (TinyML.Subst.update γ x (ρ'.lookup .value v.name)) := by
  intro y y' hmem
  by_cases hyx : y == x
  · simp [List.lookup, hyx] at hmem; subst hmem
    exact ⟨hvty, by simp [TinyML.Subst.update, hyx]⟩
  · simp [List.lookup, hyx] at hmem
    obtain ⟨hsort, hγ⟩ := hagree y y' hmem
    have hmem_snd : y' ∈ B.map Prod.snd := by
      obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hmem
      exact List.mem_map.mpr ⟨(y, y'), by rw [heq]; simp, rfl⟩
    have hρ := hρ_agree y' hmem_snd
    rw [hsort] at hρ
    exact ⟨hsort, by simp [TinyML.Subst.update, hyx]; exact hγ.trans (congrArg some hρ.symm)⟩


-- ---------------------------------------------------------------------------
-- FiniteSubst
-- ---------------------------------------------------------------------------

structure FiniteSubst where
  subst : Subst
  dom   : List Var
  range : List Var

def FiniteSubst.id : FiniteSubst where
  subst := Subst.id
  dom   := []
  range := []

def FiniteSubst.wf (σ : FiniteSubst) (decls : List Var) : Prop :=
  σ.subst.wfIn σ.dom σ.range ∧ σ.range ⊆ decls

def FiniteSubst.rename (σ : FiniteSubst) (v : Var) (name' : String) : FiniteSubst where
  subst := σ.subst.update v.sort v.name (.var v.sort name')
  dom   := v :: σ.dom
  range := ⟨name', v.sort⟩ :: σ.range

theorem agreeOn_update_fresh {ρ : Env} {v : Var} {u : v.sort.denote}
    {decls : List Var} (hfresh : v.name ∉ decls.map Var.name) :
    Env.agreeOn decls ρ (ρ.update v.sort v.name u) := by
  intro w hw
  have hne : w.name ≠ v.name := by
    intro heq; exact hfresh (heq ▸ List.mem_map.mpr ⟨w, hw, rfl⟩)
  exact (Env.lookup_update_ne (Or.inl hne)).symm

theorem FiniteSubst.rename_wf {σ : FiniteSubst} {v : Var} {name' : String} {decls : List Var}
    (hσ : σ.wf decls) (_hfresh : ⟨name', v.sort⟩ ∉ σ.range) :
    (σ.rename v name').wf (⟨name', v.sort⟩ :: decls) := by
  refine ⟨?_, List.cons_subset_cons _ hσ.2⟩
  -- (σ.rename v name').subst.wfIn (v :: σ.dom) (⟨name', v.sort⟩ :: σ.range)
  apply Subst.wfIn_update (Subst.wfIn_mono hσ.1 (List.subset_cons_of_subset _ (List.Subset.refl _)))
  intro w hw
  simp [Term.freeVars] at hw
  exact hw ▸ List.mem_cons_self ..

theorem FiniteSubst.rename_agreeOn {σ : FiniteSubst} {v : Var} {name' : String}
    {ρ : Env} {u : v.sort.denote}
    (hσwf : σ.subst.wfIn σ.dom σ.range) (hfresh : ⟨name', v.sort⟩ ∉ σ.range) :
    Env.agreeOn (v :: σ.dom)
      ((σ.rename v name').subst.eval (ρ.update v.sort name' u))
      ((σ.subst.eval ρ).update v.sort v.name u) :=
  Subst.eval_update_agreeOn hσwf hfresh

theorem FiniteSubst.eval_update_fresh {σ : FiniteSubst} {ρ : Env} {τ : Srt} {name' : String}
    {u : τ.denote} (hσ : σ.subst.wfIn σ.dom σ.range) (hfresh : ⟨name', τ⟩ ∉ σ.range) :
    Env.agreeOn σ.dom (σ.subst.eval ρ) (σ.subst.eval (ρ.update τ name' u)) := by
  intro w hw
  simp only [Subst.eval_lookup]
  exact (Term.eval_update_fresh (fun hfv => hfresh (hσ w hw _ hfv))).symm

theorem FiniteSubst.subst_wfIn_formula {σ : FiniteSubst} {φ : Formula} {decls : List Var}
    (hσ : σ.wf decls) (hφ : φ.wfIn σ.dom) : (φ.subst σ.subst σ.range).wfIn decls := by
  have h1 : σ.subst.wfIn σ.dom σ.range := hσ.1
  have h2 : (φ.subst σ.subst σ.range).wfIn σ.range := Formula.subst_wfIn hφ h1
  exact Formula.wfIn_mono _ h2 hσ.2

theorem FiniteSubst.eval_subst_formula {σ : FiniteSubst} {φ : Formula} {ρ : Env}
    (hφ : φ.wfIn σ.dom) (hσ : σ.subst.wfIn σ.dom σ.range) :
    (φ.subst σ.subst σ.range).eval ρ ↔ φ.eval (σ.subst.eval ρ) :=
  Formula.eval_subst hφ hσ

theorem FiniteSubst.id_wf (decls : List Var) : FiniteSubst.id.wf decls := by
  constructor
  · intro v hv; simp [FiniteSubst.id] at hv
  · intro v hv; simp [FiniteSubst.id] at hv

theorem FiniteSubst.eval_agreeOn {σ : FiniteSubst} {ρ ρ' : Env}
    (hσ : σ.subst.wfIn σ.dom σ.range) (hagree : Env.agreeOn σ.range ρ ρ') :
    Env.agreeOn σ.dom (σ.subst.eval ρ) (σ.subst.eval ρ') := by
  intro v hv
  simp only [Subst.eval_lookup]
  exact Term.eval_env_agree (hσ v hv) hagree

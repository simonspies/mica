import Mica.SeparationLogic.Axioms
import Mica.SeparationLogic.SpatialAtom

open Iris Iris.BI

/-! # Spatial Atoms and Contexts — Iris Interpretation

The syntactic definitions (`SpatialAtom`, `SpatialContext`, `wfIn`, `find`,
`remove`) live in `Mica.SeparationLogic.SpatialAtom`. This file adds the
Iris-level interpretation and related lemmas. -/

namespace SpatialAtom

/-- Iris interpretation of a single spatial atom. -/
def interp (ρ : Env) : SpatialAtom → iProp
  | .pointsTo l v => ∃ (loc : Runtime.Location),
      ⌜Term.eval ρ l = .loc loc⌝ ∗ loc ↦ Term.eval ρ v

/-- Interpreting a well-formed atom only depends on the environment values of
    symbols in the ambient signature. -/
theorem interp_env_agree {a : SpatialAtom} {Δ : Signature} {ρ ρ' : Env}
    (hwf : a.wfIn Δ) (hagree : Env.agreeOn Δ ρ ρ') :
    interp ρ a = interp ρ' a := by
  cases a with
  | pointsTo l v =>
    simp only [interp]
    rw [Term.eval_env_agree hwf.1 hagree, Term.eval_env_agree hwf.2 hagree]

/-- If a points-to atom's location term evaluates to `loc`, its interpretation
    is equivalent to the raw points-to assertion for `loc`. -/
theorem interp_pointsTo {ρ : Env} {lt vt : Term .value} {loc : Runtime.Location}
    (hloc : Term.eval ρ lt = .loc loc) :
    interp ρ (.pointsTo lt vt) ⊣⊢ loc ↦ Term.eval ρ vt := by
  constructor
  · simp only [interp]
    istart
    iintro ⟨%loc', %Hloc', Hpt⟩
    have : loc' = loc := Runtime.Val.loc.inj (Hloc'.symm.trans hloc)
    subst this
    iexact Hpt
  · simp only [interp]
    istart
    iintro Hpt
    iexists loc
    isplitr
    · ipure_intro
      exact hloc
    · iexact Hpt

end SpatialAtom

namespace SpatialContext

/-- Iris interpretation of a spatial context: the separating conjunction of all items. -/
def interp (ρ : Env) : SpatialContext → iProp
  | []     => emp
  | a :: Γ => a.interp ρ ∗ interp ρ Γ

/-- Interpreting a well-formed context only depends on the environment values of
    symbols in the ambient signature. -/
theorem interp_env_agree {ctx : SpatialContext} {Δ : Signature} {ρ ρ' : Env}
    (hwf : wfIn ctx Δ) (hagree : Env.agreeOn Δ ρ ρ') :
    interp ρ ctx = interp ρ' ctx := by
  induction ctx with
  | nil => simp [interp]
  | cons a ctx ih =>
    have ha : SpatialAtom.interp ρ a = SpatialAtom.interp ρ' a :=
      SpatialAtom.interp_env_agree (hwf a (by simp)) hagree
    have htail : wfIn ctx Δ := (wfIn_cons a ctx Δ).1 hwf |>.2
    have hctx : interp ρ ctx = interp ρ' ctx :=
      ih htail
    simp [interp, ha, hctx]

@[simp] theorem interp_nil (ρ : Env) : interp ρ [] = emp := rfl
@[simp] theorem interp_cons (ρ : Env) (a : SpatialAtom) (Γ : SpatialContext) :
    interp ρ (a :: Γ) = (a.interp ρ ∗ interp ρ Γ) := rfl

@[simp] theorem interp_insert (ρ : Env) (a : SpatialAtom) (ctx : SpatialContext) :
    interp ρ (insert a ctx) = (a.interp ρ ∗ interp ρ ctx) := rfl

private theorem sep_comm3 {A B C : iProp} : A ∗ (B ∗ C) ⊣⊢ B ∗ (A ∗ C) :=
  ⟨sep_assoc.2 |>.trans (sep_mono_l sep_comm.1) |>.trans sep_assoc.1,
   sep_assoc.2 |>.trans (sep_mono_l sep_comm.2) |>.trans sep_assoc.1⟩

/-- The interpretation of a context is equivalent to splitting off the atom at index `n`. -/
theorem interp_remove (ρ : Env) (ctx : SpatialContext) (n : Nat)
    (a : SpatialAtom) (rest : SpatialContext)
    (h : remove ctx n = some (a, rest)) :
    interp ρ ctx ⊣⊢ a.interp ρ ∗ interp ρ rest := by
  induction ctx generalizing n a rest with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero =>
      simp [remove] at h; obtain ⟨rfl, rfl⟩ := h; simp [interp]
    | succ n =>
      simp only [remove_cons_succ] at h
      match hr : remove xs n, h with
      | some (b, rest'), h =>
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨sep_mono_r (ih n b rest' hr).1 |>.trans sep_comm3.1,
               sep_comm3.2 |>.trans (sep_mono_r (ih n b rest' hr).2)⟩


end SpatialContext

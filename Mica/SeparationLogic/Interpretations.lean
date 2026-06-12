-- SUMMARY: Iris interpretations of spatial atoms and contexts, with lemmas relating syntax to separation-logic assertions.
import Mica.SeparationLogic.Axioms
import Mica.SeparationLogic.SpatialAtom
import Mica.TinyML.Types

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]

/-! # Spatial Atoms and Contexts — Iris Interpretation

The syntactic definitions (`SpatialAtom`, `SpatialContext`, `wfIn`, `find`,
`remove`, and single-atom `SpatialAtom.interp`) live in
`Mica.SeparationLogic.SpatialAtom`. This file adds context-level
interpretation and related lemmas. -/

namespace SpatialAtom

/-- Interpreting a well-formed atom only depends on the environment values of
    symbols in the ambient signature. -/
theorem interp_env_agree (Θ : TinyML.TypeEnv) {a : SpatialAtom} {Δ : Signature} {ρ ρ' : Env}
    (hwf : a.wfIn Δ) (hagree : Env.agreeOn Δ ρ ρ') :
    interp Θ ρ a ⊣⊢ interp Θ ρ' a := by
  cases a with
  | pointsTo l v ty =>
    simp only [interp, Term.eval_env_agree hwf.1 hagree, Term.eval_env_agree hwf.2 hagree]
    exact ⟨BIBase.Entails.rfl, BIBase.Entails.rfl⟩

/-- If a points-to atom's location term evaluates to `loc`, its interpretation
    is equivalent to the raw heap ownership together with the bundled value
    typing fact. -/
theorem interp_pointsTo (Θ : TinyML.TypeEnv) {ρ : Env} {lt vt : Term .value}
    {ty : TinyML.Typ} {loc : Runtime.Location}
    (hloc : Term.eval ρ lt = .loc loc) :
    interp Θ ρ (.pointsTo lt vt ty) ⊣⊢
      loc ↦ Term.eval ρ vt ∗ TinyML.ValHasType Θ (Term.eval ρ vt) ty := by
  constructor
  · simp only [interp]
    istart
    iintro ⟨%loc', %Hloc', Hpt, Hty⟩
    have : loc' = loc := Runtime.Val.loc.inj (Hloc'.symm.trans hloc)
    subst this
    isplitl [Hpt]
    · iexact Hpt
    · iexact Hty
  · simp only [interp]
    istart
    iintro ⟨Hpt, Hty⟩
    iexists loc
    isplitr
    · ipureintro
      exact hloc
    · isplitl [Hpt]
      · iexact Hpt
      · iexact Hty

end SpatialAtom

namespace SpatialContext

/-- Iris interpretation of a spatial context: the separating conjunction of all items. -/
def interp (Θ : TinyML.TypeEnv) (ρ : Env) : SpatialContext → iProp
  | []     => emp
  | a :: Γ => a.interp Θ ρ ∗ interp Θ ρ Γ

/-- Interpreting a well-formed context only depends on the environment values of
    symbols in the ambient signature. -/
theorem interp_env_agree (Θ : TinyML.TypeEnv) {ctx : SpatialContext} {Δ : Signature} {ρ ρ' : Env}
    (hwf : wfIn ctx Δ) (hagree : Env.agreeOn Δ ρ ρ') :
    interp Θ ρ ctx ⊣⊢ interp Θ ρ' ctx := by
  induction ctx with
  | nil => simp [interp]
  | cons a ctx ih =>
    have ha : SpatialAtom.interp Θ ρ a ⊣⊢ SpatialAtom.interp Θ ρ' a :=
      SpatialAtom.interp_env_agree Θ (hwf a (by simp)) hagree
    have htail : wfIn ctx Δ := (wfIn_cons a ctx Δ).1 hwf |>.2
    have hctx : interp Θ ρ ctx ⊣⊢ interp Θ ρ' ctx := ih htail
    simp only [interp]
    exact ⟨sep_mono ha.1 hctx.1, sep_mono ha.2 hctx.2⟩

@[simp] theorem interp_nil (Θ : TinyML.TypeEnv) (ρ : Env) : interp Θ ρ [] = emp := rfl
@[simp] theorem interp_cons (Θ : TinyML.TypeEnv) (ρ : Env) (a : SpatialAtom) (Γ : SpatialContext) :
    interp Θ ρ (a :: Γ) = (a.interp Θ ρ ∗ interp Θ ρ Γ) := rfl

@[simp] theorem interp_insert (Θ : TinyML.TypeEnv) (ρ : Env) (a : SpatialAtom) (ctx : SpatialContext) :
    interp Θ ρ (insert a ctx) = (a.interp Θ ρ ∗ interp Θ ρ ctx) := rfl

omit [MicaGS HasLC.hasLC Sig] in
private theorem sep_comm3 {A B C : iProp} : A ∗ (B ∗ C) ⊣⊢ B ∗ (A ∗ C) :=
  ⟨sep_assoc.2 |>.trans (sep_mono_left sep_comm.1) |>.trans sep_assoc.1,
   sep_assoc.2 |>.trans (sep_mono_left sep_comm.2) |>.trans sep_assoc.1⟩

/-- The interpretation of a context is equivalent to splitting off the atom at index `n`. -/
theorem interp_remove (Θ : TinyML.TypeEnv) (ρ : Env) (ctx : SpatialContext) (n : Nat)
    (a : SpatialAtom) (rest : SpatialContext)
    (h : remove ctx n = some (a, rest)) :
    interp Θ ρ ctx ⊣⊢ a.interp Θ ρ ∗ interp Θ ρ rest := by
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
        exact ⟨sep_mono_right (ih n b rest' hr).1 |>.trans sep_comm3.1,
               sep_comm3.2 |>.trans (sep_mono_right (ih n b rest' hr).2)⟩


end SpatialContext

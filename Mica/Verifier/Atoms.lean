import Mica.FOL.Printing
import Mica.FOL.Subst

/-!
# Atoms

Defines `Atom`, a sort predicate that asserts a value-sorted term has a specific sort
and extracts the underlying typed value.
-/


-- ---------------------------------------------------------------------------
-- Atom inductive
-- ---------------------------------------------------------------------------

/-- A sort predicate: asserts that a value-sorted term has a specific sort,
    and extracts the underlying typed value. -/
inductive Atom : Srt → Type where
  | isint  : Term .value → Atom .int
  | isbool : Term .value → Atom .bool


-- ---------------------------------------------------------------------------
-- Substitution
-- ---------------------------------------------------------------------------

def Atom.subst (σ : Subst) : Atom τ → Atom τ
  | .isint t  => .isint (t.subst σ)
  | .isbool t => .isbool (t.subst σ)


-- ---------------------------------------------------------------------------
-- Conversion to formula
-- ---------------------------------------------------------------------------

/-- Convert an atom applied to a typed term into a formula. -/
def Atom.toFormula : Atom τ → Term τ → Formula
  | .isint  v, t => .eq .value v (.unop .ofInt t)
  | .isbool v, t => .eq .value v (.unop .ofBool t)

/-- Try to match a formula against an atom, returning the extracted term if it matches. -/
def Formula.matchAtom (φ : Formula) (a : Atom τ) : Option (Term τ) :=
  match a with
  | .isint v =>
    match φ with
    | .eq .value v' (.unop .ofInt t) => if v' = v then some t else none
    | _ => none
  | .isbool v =>
    match φ with
    | .eq .value v' (.unop .ofBool t) => if v' = v then some t else none
    | _ => none

theorem Formula.matchAtom_correct {φ : Formula} {a : Atom τ} {t : Term τ}
    (h : φ.matchAtom a = some t) : φ = a.toFormula t := by
  cases a with
  | isint v =>
    simp only [Formula.matchAtom] at h
    split at h <;> simp_all; obtain ⟨rfl, rfl⟩ := h; rfl
  | isbool v =>
    simp only [Formula.matchAtom] at h
    split at h <;> simp_all; obtain ⟨rfl, rfl⟩ := h; rfl


-- ---------------------------------------------------------------------------
-- Resolution
-- ---------------------------------------------------------------------------

/-- Resolve an atom against a list of formulas. -/
def Atom.resolve (a : Atom τ) (C : List Formula) : Option (Term τ) :=
  C.findSome? (·.matchAtom a)

theorem Atom.resolve_correct {a : Atom τ} {C : List Formula} {t : Term τ}
    (h : a.resolve C = some t) (ρ : Env) (hC : ∀ φ ∈ C, φ.eval ρ) :
    (a.toFormula t).eval ρ := by
  obtain ⟨φ, hφ_mem, hφ_match⟩ := List.exists_of_findSome?_eq_some h
  have heq := Formula.matchAtom_correct hφ_match
  subst heq
  exact hC _ hφ_mem

theorem Atom.resolve_wfIn {a : Atom τ} {C : List Formula} {t : Term τ} {decls : List Var}
    (h : a.resolve C = some t) (hwf : ∀ φ ∈ C, φ.wfIn decls) :
    t.wfIn decls := by
  obtain ⟨φ, hφ_mem, hφ_match⟩ := List.exists_of_findSome?_eq_some h
  have heq := Formula.matchAtom_correct hφ_match
  subst heq
  intro v hv
  apply hwf _ hφ_mem
  cases a with
  | isint u =>
    simp only [Atom.toFormula, Formula.freeVars, Term.freeVars] at hv ⊢
    exact List.mem_append_right _ hv
  | isbool u =>
    simp only [Atom.toFormula, Formula.freeVars, Term.freeVars] at hv ⊢
    exact List.mem_append_right _ hv


-- ---------------------------------------------------------------------------
-- Printer
-- ---------------------------------------------------------------------------

def Atom.toStringHum : {τ : Srt} → Atom τ → String
  | _, .isint  t => s!"isint {t.toStringHum}"
  | _, .isbool t => s!"isbool {t.toStringHum}"


-- ---------------------------------------------------------------------------
-- Semantics
-- ---------------------------------------------------------------------------

def Atom.eval {τ : Srt} (p : Atom τ) (ρ : Env) : τ.denote → Prop :=
  match p with
  | isint t  => λ v => .int v = t.eval ρ
  | isbool t => λ v => .bool v = t.eval ρ


-- ---------------------------------------------------------------------------
-- Well-formedness
-- ---------------------------------------------------------------------------

/-- An atom is well-formed in a list of declared variables. -/
def Atom.wfIn (decls : List Var) : Atom τ → Prop
  | .isint t  => t.wfIn decls
  | .isbool t => t.wfIn decls

def Atom.checkWf (p : Atom τ) (Δ : VarCtx) : Except String Unit :=
  match p with
  | .isint t  => t.checkWf Δ
  | .isbool t => t.checkWf Δ

theorem Atom.checkWf_ok {p : Atom τ} {Δ : VarCtx} (h : p.checkWf Δ = .ok ()) : p.wfIn Δ := by
  cases p with
  | isint t  => exact Term.checkWf_ok h
  | isbool t => exact Term.checkWf_ok h

theorem Atom.wfIn_mono {p : Atom τ} {decls decls' : List Var}
    (h : p.wfIn decls) (hmono : ∀ v ∈ decls, v ∈ decls') : p.wfIn decls' := by
  cases p with
  | isint t  => exact fun w hw => hmono _ (h w hw)
  | isbool t => exact fun w hw => hmono _ (h w hw)

theorem Atom.eval_env_agree {p : Atom τ} {ρ ρ' : Env} {Δ : VarCtx}
    (hwf : p.wfIn Δ) (hagree : Env.agreeOn Δ ρ ρ') : p.eval ρ = p.eval ρ' := by
  cases p with
  | isint t  => simp [Atom.eval, Term.eval_env_agree hwf hagree]
  | isbool t => simp [Atom.eval, Term.eval_env_agree hwf hagree]

theorem Atom.toFormula_wfIn {p : Atom τ} {t : Term τ} {decls : List Var}
    (hp : p.wfIn decls) (ht : t.wfIn decls) :
    (p.toFormula t).wfIn decls := by
  cases p with
  | isint v =>
    simp only [Atom.toFormula, Formula.wfIn, Formula.freeVars, Term.freeVars, List.mem_append]
    intro w hw; exact hw.elim (hp w ·) (ht w ·)
  | isbool v =>
    simp only [Atom.toFormula, Formula.wfIn, Formula.freeVars, Term.freeVars, List.mem_append]
    intro w hw; exact hw.elim (hp w ·) (ht w ·)

theorem Atom.toFormula_eval_iff {p : Atom τ} {t : Term τ} {ρ : Env} :
    (p.toFormula t).eval ρ ↔ p.eval ρ (t.eval ρ) := by
  cases p with
  | isint v  => simp [Atom.toFormula, Atom.eval, Formula.eval, Term.eval, eq_comm]
  | isbool v => simp [Atom.toFormula, Atom.eval, Formula.eval, Term.eval, eq_comm]

/-- If `p.eval ρ u` holds and `p` is wfIn fresh decls, then `p.toFormula (.var τ x)` holds
    after updating `ρ` with `x ↦ u`. -/
theorem Atom.toFormula_eval_1 {p : Atom τ} {ρ : Env}  :
     p.eval ρ (t.eval ρ) → (p.toFormula t).eval ρ :=
  Atom.toFormula_eval_iff.mpr

/-- If `(p.toFormula t).eval ρ` holds, then `p.eval ρ (t.eval ρ)`. -/
theorem Atom.toFormula_eval_2 {p : Atom τ} {t : Term τ} {ρ : Env}
    (h : (p.toFormula t).eval ρ) : p.eval ρ (t.eval ρ) :=
  Atom.toFormula_eval_iff.mp h


-- ---------------------------------------------------------------------------
-- Substitution lemmas
-- ---------------------------------------------------------------------------

theorem Atom.eval_subst {p : Atom τ} {σ : Subst} {ρ : Env} :
    (p.subst σ).eval ρ = p.eval (σ.eval ρ) := by
  cases p with
  | isint t  => simp [Atom.subst, Atom.eval, Term.eval_subst]
  | isbool t => simp [Atom.subst, Atom.eval, Term.eval_subst]

theorem Atom.subst_wfIn {p : Atom τ} {σ : Subst} {Δ Δ' : VarCtx}
    (hp : p.wfIn Δ) (hσ : σ.wfIn Δ Δ') : (p.subst σ).wfIn Δ' := by
  cases p with
  | isint t  => exact Term.subst_wfIn hp hσ
  | isbool t => exact Term.subst_wfIn hp hσ

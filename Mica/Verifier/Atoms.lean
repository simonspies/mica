import Mica.FOL.Printing
import Mica.FOL.Subst
import Mica.Verifier.Monad

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
  | isinj  (tag : Nat) (arity : Nat) : Term .value → Atom .value


-- ---------------------------------------------------------------------------
-- Substitution
-- ---------------------------------------------------------------------------

def Atom.subst (σ : Subst) : Atom τ → Atom τ
  | .isint t  => .isint (t.subst σ)
  | .isbool t => .isbool (t.subst σ)
  | .isinj tag arity t => .isinj tag arity (t.subst σ)


-- ---------------------------------------------------------------------------
-- Conversion to formula
-- ---------------------------------------------------------------------------

/-- Convert an atom applied to a typed term into a formula. -/
def Atom.toFormula : Atom τ → Term τ → Formula
  | .isint  v, t => .eq .value v (.unop .ofInt t)
  | .isbool v, t => .eq .value v (.unop .ofBool t)
  | .isinj tag arity v, t => .eq .value v (.unop (.mkInj tag arity) t)

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
  | .isinj tag arity v =>
    match φ with
    | .eq .value v' (.unop (.mkInj tag' arity') t) =>
      if v' = v ∧ tag = tag' ∧ arity = arity' then some t else none
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
  | isinj tag arity v =>
    simp only [Formula.matchAtom] at h
    split at h <;> simp_all
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h; rfl


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

theorem Atom.resolve_wfIn {a : Atom τ} {C : List Formula} {t : Term τ} {Δ : Signature}
    (h : a.resolve C = some t) (hwf : ∀ φ ∈ C, φ.wfIn Δ) :
    t.wfIn Δ := by
  obtain ⟨φ, hφ_mem, hφ_match⟩ := List.exists_of_findSome?_eq_some h
  have heq := Formula.matchAtom_correct hφ_match
  subst heq
  have hφwf := hwf _ hφ_mem
  cases a with
  | isint u =>
    simp only [Atom.toFormula, Formula.wfIn, Term.wfIn] at hφwf
    exact hφwf.2.2
  | isbool u =>
    simp only [Atom.toFormula, Formula.wfIn, Term.wfIn] at hφwf
    exact hφwf.2.2
  | isinj tag arity u =>
    simp only [Atom.toFormula, Formula.wfIn, Term.wfIn] at hφwf
    exact hφwf.2.2


-- ---------------------------------------------------------------------------
-- Printer
-- ---------------------------------------------------------------------------

def Atom.toStringHum : {τ : Srt} → Atom τ → String
  | _, .isint  t => s!"isint {t.toStringHum}"
  | _, .isbool t => s!"isbool {t.toStringHum}"
  | _, .isinj tag arity t => s!"isinj {tag}/{arity} {t.toStringHum}"


-- ---------------------------------------------------------------------------
-- Semantics
-- ---------------------------------------------------------------------------

def Atom.eval {τ : Srt} (p : Atom τ) (ρ : Env) : τ.denote → Prop :=
  match p with
  | isint t  => λ v => .int v = t.eval ρ
  | isbool t => λ v => .bool v = t.eval ρ
  | isinj tag arity t => λ v => .inj tag arity v = t.eval ρ


-- ---------------------------------------------------------------------------
-- Well-formedness
-- ---------------------------------------------------------------------------

/-- An atom is well-formed in a signature. -/
def Atom.wfIn (Δ : Signature) : Atom τ → Prop
  | .isint t  => t.wfIn Δ
  | .isbool t => t.wfIn Δ
  | .isinj _ _ t => t.wfIn Δ

def Atom.checkWf (p : Atom τ) (Δ : Signature) : Except String Unit :=
  match p with
  | .isint t  => t.checkWf Δ
  | .isbool t => t.checkWf Δ
  | .isinj _ _ t => t.checkWf Δ

theorem Atom.checkWf_ok {p : Atom τ} {Δ : Signature} (h : p.checkWf Δ = .ok ()) : p.wfIn Δ := by
  cases p with
  | isint t  => exact Term.checkWf_ok h
  | isbool t => exact Term.checkWf_ok h
  | isinj tag arity t => exact Term.checkWf_ok h

theorem Atom.wfIn_mono {p : Atom τ} {Δ Δ' : Signature}
    (h : p.wfIn Δ) (hmono : Δ.Subset Δ') (hwf : Δ'.wf) : p.wfIn Δ' := by
  cases p with
  | isint t  => exact Term.wfIn_mono t h hmono hwf
  | isbool t => exact Term.wfIn_mono t h hmono hwf
  | isinj tag arity t => exact Term.wfIn_mono t h hmono hwf

theorem Atom.eval_env_agree {p : Atom τ} {ρ ρ' : Env} {Δ : Signature}
    (hwf : p.wfIn Δ) (hagree : Env.agreeOn Δ ρ ρ') : p.eval ρ = p.eval ρ' := by
  cases p with
  | isint t  => simp [Atom.eval, Term.eval_env_agree hwf hagree]
  | isbool t => simp [Atom.eval, Term.eval_env_agree hwf hagree]
  | isinj tag arity t => simp [Atom.eval, Term.eval_env_agree hwf hagree]

theorem Atom.toFormula_wfIn {p : Atom τ} {t : Term τ} {Δ : Signature}
    (hp : p.wfIn Δ) (ht : t.wfIn Δ) :
    (p.toFormula t).wfIn Δ := by
  cases p with
  | isint v =>
    simp only [Atom.toFormula, Formula.wfIn, Term.wfIn]
    exact ⟨hp, trivial, ht⟩
  | isbool v =>
    simp only [Atom.toFormula, Formula.wfIn, Term.wfIn]
    exact ⟨hp, trivial, ht⟩
  | isinj tag arity v =>
    simp only [Atom.toFormula, Formula.wfIn, Term.wfIn]
    exact ⟨hp, trivial, ht⟩

theorem Atom.toFormula_eval_iff {p : Atom τ} {t : Term τ} {ρ : Env} :
    (p.toFormula t).eval ρ ↔ p.eval ρ (t.eval ρ) := by
  cases p with
  | isint v  => simp [Atom.toFormula, Atom.eval, Formula.eval, Term.eval, eq_comm]
  | isbool v => simp [Atom.toFormula, Atom.eval, Formula.eval, Term.eval, eq_comm]
  | isinj tag arity v => simp [Atom.toFormula, Atom.eval, Formula.eval, Term.eval, eq_comm]

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

theorem Atom.eval_subst {p : Atom τ} {σ : Subst} {ρ : Env} {Δ Δ' : Signature}
    (hp : p.wfIn Δ) (hσ : σ.wfIn Δ.vars Δ') (hwfΔ' : Δ'.wf) :
    (p.subst σ).eval ρ = p.eval (σ.eval ρ) := by
  cases p with
  | isint t =>
    funext v
    simp only [Atom.subst, Atom.eval]
    rw [Term.eval_subst hp hσ hwfΔ']
  | isbool t =>
    funext v
    simp only [Atom.subst, Atom.eval]
    rw [Term.eval_subst hp hσ hwfΔ']
  | isinj tag arity t =>
    funext v
    simp only [Atom.subst, Atom.eval]
    rw [Term.eval_subst hp hσ hwfΔ']

theorem Atom.subst_wfIn {p : Atom τ} {σ : Subst} {dom : VarCtx} {Δ Δ' : Signature}
    (hp : p.wfIn Δ) (hσ : σ.wfIn dom Δ') (hdom : Δ.vars ⊆ dom)
    (hsymbols : Δ.SymbolSubset Δ')
    (hwf : Δ'.wf) :
    (p.subst σ).wfIn Δ' := by
  cases p with
  | isint t  => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | isbool t => exact Term.subst_wfIn hp hσ hdom hsymbols hwf
  | isinj tag arity t => exact Term.subst_wfIn hp hσ hdom hsymbols hwf


-- ---------------------------------------------------------------------------
-- Candidates: guarded resolution alternatives
-- ---------------------------------------------------------------------------

/-- Candidate resolutions for an atom, each guarded by a provability condition.
    Each pair `(φ, t)` means: if `φ` is provable, then `t` resolves the atom. -/
def Atom.candidates : Atom τ → List (Formula × Term τ)
  | .isint  v => [(.unpred .isInt v, .unop .toInt v)]
  | .isbool v => [(.unpred .isBool v, .unop .toBool v)]
  | .isinj tag arity v => [(.unpred (.isInj tag arity) v, .unop .payloadOf v)]

theorem Atom.candidates_correct {a : Atom τ} {φ : Formula} {t : Term τ} {ρ : Env}
    (hmem : (φ, t) ∈ a.candidates) (h : φ.eval ρ) : (a.toFormula t).eval ρ := by
  cases a with
  | isint v =>
    simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem
    simp [Formula.eval, UnPred.eval] at h
    simp [toFormula, Formula.eval, Term.eval, UnOp.eval]
    cases hv : v.eval ρ <;> simp_all
  | isbool v =>
    simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem
    simp [Formula.eval, UnPred.eval] at h
    simp [toFormula, Formula.eval, Term.eval, UnOp.eval]
    cases hv : v.eval ρ <;> simp_all
  | isinj tag arity v =>
    simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem
    simp [Formula.eval, UnPred.eval] at h
    simp [toFormula, Formula.eval, Term.eval, UnOp.eval]
    cases hv : v.eval ρ <;> simp_all

theorem Atom.candidates_wfIn {a : Atom τ} {φ : Formula} {t : Term τ} {Δ : Signature}
    (hmem : (φ, t) ∈ a.candidates) (h : a.wfIn Δ) : φ.wfIn Δ ∧ t.wfIn Δ := by
  cases a with
  | isint v  => simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem; exact ⟨h, trivial, h⟩
  | isbool v => simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem; exact ⟨h, trivial, h⟩
  | isinj tag arity v => simp [candidates] at hmem; obtain ⟨rfl, rfl⟩ := hmem; exact ⟨h, trivial, h⟩


-- ---------------------------------------------------------------------------
-- VerifM integration
-- ---------------------------------------------------------------------------

/-- Try candidate resolutions in order, checking each guard via the SMT solver. -/
def VerifM.tryCandidates : List (Formula × Term τ) → VerifM (Option (Term τ))
  | [] => pure none
  | (φ, t) :: rest => do
    if ← VerifM.check φ then pure (some t)
    else VerifM.tryCandidates rest

private theorem VerifM.eval_tryCandidates
    {candidates : List (Formula × Term τ)} {a : Atom τ}
    {st : TransState} {ρ : Env} {Q : Option (Term τ) → TransState → Env → Prop}
    (h : VerifM.eval (VerifM.tryCandidates candidates) st ρ Q)
    (hcands : ∀ p ∈ candidates, p ∈ a.candidates)
    (hpwf : a.wfIn st.decls) :
    ∃ result : Option (Term τ),
      Q result st ρ
      ∧ (∀ t, result = some t → (a.toFormula t).eval ρ)
      ∧ (∀ t, result = some t → t.wfIn st.decls) := by
  induction candidates with
  | nil =>
    simp [tryCandidates] at h
    exact ⟨none, VerifM.eval_ret h,
           fun _ ht => absurd ht (by simp), fun _ ht => absurd ht (by simp)⟩
  | cons c rest ih =>
    obtain ⟨φ, t⟩ := c
    simp [tryCandidates] at h
    have hb := VerifM.eval_bind _ _ _ _ h
    have hmem := hcands (φ, t) (List.mem_cons_self ..)
    have ⟨φwf, twf⟩ := Atom.candidates_wfIn hmem hpwf
    have ⟨b, hb_sound, hq⟩ := VerifM.eval_check hb φwf
    cases b with
    | true =>
      simp at hq
      exact ⟨some t, VerifM.eval_ret hq,
             fun t' ht' => by cases ht'; exact Atom.candidates_correct hmem (hb_sound rfl),
             fun t' ht' => by cases ht'; exact twf⟩
    | false =>
      simp at hq
      exact ih hq (fun p hp => hcands p (List.mem_cons_of_mem _ hp))

/-- Look up an atom in the assertion context.
    Tier 1: syntactic search through the context.
    Tier 2: try candidate resolutions via the SMT solver. -/
def VerifM.resolve (a : Atom τ) : VerifM (Option (Term τ)) := do
  match ← VerifM.ctxPure (a.resolve ·) with
  | some t => pure (some t)
  | none => VerifM.tryCandidates a.candidates

theorem VerifM.eval_resolve {pred : Atom τ} {st : TransState} {ρ : Env}
    {Q : Option (Term τ) → TransState → Env → Prop}
    (h : VerifM.eval (VerifM.resolve pred) st ρ Q)
    (hpwf : pred.wfIn st.decls) :
    ∃ result : Option (Term τ),
      Q result st ρ
      ∧ (∀ t, result = some t → (pred.toFormula t).eval ρ)
      ∧ (∀ t, result = some t → t.wfIn st.decls) := by
  unfold VerifM.resolve at h
  have hb1 := VerifM.eval_bind _ _ _ _ h
  have ⟨hctx_q, hholds, hwfAsserts⟩ := VerifM.eval_ctxPure hb1
  cases hres : pred.resolve st.asserts with
  | some t =>
    simp [hres] at hctx_q
    exact ⟨some t, VerifM.eval_ret hctx_q,
           fun t' ht' => by cases ht'; exact Atom.resolve_correct hres ρ hholds,
           fun t' ht' => by cases ht'; exact Atom.resolve_wfIn hres hwfAsserts⟩
  | none =>
    simp [hres] at hctx_q
    exact eval_tryCandidates hctx_q (fun p hp => hp) hpwf

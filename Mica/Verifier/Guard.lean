-- SUMMARY: The guard constant deactivating quantified axioms in low-effort checks, effort levels, and guarded axioms.
import Mica.FOL.Formulas

/-! ## The guard constant

The verifier uses a builtin Bool constant `guard!`, declared at the start of
every run but never asserted by default. Quantified axioms are "guarded" in
the sense that `guard! = true` is added as an additional premise. The effect
is that we can enable them locally by assering `guard! = true`. To improve
performance, the guard is moved inside of quantifiers, which allows Z3 to
share quantifier instantiations across different asserts. (Otherwise, it
could only start to instantiate them once the guard is enabled.) -/

def guardConst : FOL.Const := ⟨"guard!", .bool⟩

/-- The formula pinning the guard to true; asserted inside high-effort checks. -/
def guardFormula : Formula :=
  .eq .bool (.const (.uninterpreted guardConst.name guardConst.sort)) (.const (.b true))

/-- The formula pinning the guard to false; used only inside fast low-effort
probes whose positive result is never trusted as a proof. -/
def guardFalseFormula : Formula :=
  .eq .bool (.const (.uninterpreted guardConst.name guardConst.sort)) (.const (.b false))

/-- A signature supports guarding if the guard constant is declared. -/
def Signature.supportsGuarding (Δ : Signature) : Prop := guardConst ∈ Δ.consts

theorem Signature.supportsGuarding.mono {Δ Δ' : Signature} (hsub : Δ.Subset Δ')
    (h : Δ.supportsGuarding) : Δ'.supportsGuarding :=
  hsub.consts _ h

/-- The guard formula is well-formed in any signature declaring the guard. -/
theorem guardFormula.wf {Δ : Signature} (hwf : Δ.wf) (h : Δ.supportsGuarding) :
    guardFormula.wfIn Δ :=
  ⟨Term.const_wfIn_of_mem hwf h, trivial⟩

/-- An environment supports guarding if it maps the guard constant to true. -/
def Env.supportsGuarding (ρ : Env) : Prop := guardFormula.eval ρ

/-- Guard support transfers along environments that agree on a signature
declaring the guard. -/
theorem Env.supportsGuarding.agree {Δ : Signature} {ρ ρ' : Env}
    (hΔ : Δ.supportsGuarding) (hagree : Env.agreeOn Δ ρ ρ')
    (h : ρ.supportsGuarding) : ρ'.supportsGuarding := by
  have heq := hagree.2.1 guardConst hΔ
  simp only [guardConst] at heq
  simp only [Env.supportsGuarding, guardFormula, Formula.eval, Term.eval, Const.denote,
    guardConst] at h ⊢
  rw [← heq]
  exact h

/-- Pinning the guard constant establishes guard support. -/
theorem Env.supportsGuarding_updateConst (ρ : Env) :
    (ρ.updateConst guardConst.sort guardConst.name true).supportsGuarding := by
  simp [Env.supportsGuarding, guardFormula, Formula.eval, Term.eval, Const.denote,
    Env.updateConst, guardConst]

/-! ## Guarded formulas -/

namespace Formula

/-- Guard a formula while preserving the outer universal quantifier spine. This
keeps SMT triggers attached directly to the quantifier they were written for,
which is substantially friendlier to Z3 than placing the implication outside
the quantifier. If a binder shadows the guard name, stop pushing and guard the
whole formula. -/
def guarded : Formula → Formula
  | .forall_ x τ ps φ =>
      if x = guardConst.name then
        .implies guardFormula (.forall_ x τ ps φ)
      else
        .forall_ x τ ps φ.guarded
  | φ => .implies guardFormula φ

private theorem supportsGuarding_declVar {Δ : Signature} {x : String} {τ : Srt}
    (hguard : Δ.supportsGuarding) (hx : x ≠ guardConst.name) :
    (Δ.declVar ⟨x, τ⟩).supportsGuarding := by
  simp [Signature.supportsGuarding, Signature.declVar, Signature.addVar,
    Signature.remove, guardConst] at hguard ⊢
  exact ⟨hguard, fun h => hx h.symm⟩

/-- A true formula remains true after it is guarded. -/
theorem guarded_eval {φ : Formula} {ρ : Env} (h : φ.eval ρ) : φ.guarded.eval ρ := by
  induction φ generalizing ρ with
  | forall_ x τ ps φ ih =>
      simp only [guarded]
      split
      · exact fun _ => h
      · simp only [Formula.eval]
        intro v
        exact ih (h v)
  | true_ | false_ | eq | unpred | binpred | not | and | or | implies | exists_ =>
      simp only [guarded, Formula.eval]
      exact fun _ => h

/-- Guarding preserves well-formedness when the guard constant is declared. -/
theorem guarded_wfIn {φ : Formula} {Δ : Signature} (hwf : Δ.wf)
    (hguard : Δ.supportsGuarding) (h : φ.wfIn Δ) : φ.guarded.wfIn Δ := by
  induction φ generalizing Δ with
  | forall_ x τ ps φ ih =>
      simp only [guarded]
      split
      · exact ⟨guardFormula.wf hwf hguard, h⟩
      · exact ⟨h.1, ih (Signature.wf_declVar hwf)
          (supportsGuarding_declVar hguard ‹x ≠ guardConst.name›) h.2⟩
  | true_ | false_ | eq | unpred | binpred | not | and | or | implies | exists_ =>
      simp only [guarded, Formula.wfIn]
      exact ⟨guardFormula.wf hwf hguard, h⟩

end Formula

/-! ## Effort and guarded axioms -/

/-- Effort level of a satisfiability check: `low` leaves guarded axioms
inactive, `high` asserts the guard inside the check's scope, activating them. -/
inductive Effort where
  | low
  | high
  deriving DecidableEq, Repr

/-- A formula tagged with the minimum check effort at which it is active:
`.high` axioms are guarded and hence participate only in high-effort checks. -/
structure Axiom where
  formula : Formula
  effort : Effort

namespace Axiom

/-- The formula the verifier actually assumes for an axiom: high-effort axioms
are weakened by guarding the body under leading universal quantifiers. -/
def assert : Axiom → Formula
  | ⟨φ, .low⟩ => φ
  | ⟨φ, .high⟩ => φ.guarded

/-- The formulas the verifier actually assumes for a list of axioms. -/
def asserts (axs : List Axiom) : List Formula :=
  axs.map assert

/-- The weakened axiom holds whenever the axiom itself does. -/
theorem assert_eval {a : Axiom} {ρ : Env} (h : a.formula.eval ρ) : a.assert.eval ρ := by
  obtain ⟨φ, e⟩ := a
  cases e
  · exact h
  · exact Formula.guarded_eval h

/-- The weakened axiom is well-formed wherever the axiom is, given the guard. -/
theorem assert_wfIn {a : Axiom} {Δ : Signature} (hwf : Δ.wf)
    (hguard : Δ.supportsGuarding) (h : a.formula.wfIn Δ) : a.assert.wfIn Δ := by
  obtain ⟨φ, e⟩ := a
  cases e
  · exact h
  · exact Formula.guarded_wfIn hwf hguard h

end Axiom

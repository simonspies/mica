-- SUMMARY: Generic relation-order/fixpoint infrastructure plus environment monotonicity lemmas for term evaluation.
import Mica.FOL.Terms

namespace Fix

/-- A binary relation between `α` and `β`. -/
abbrev Rel (α β : Type) := α → β → Prop

/-- Pointwise inclusion of relations. -/
def le (R S : Rel α β) : Prop := ∀ a b, R a b → S a b

/-- Monotone operator on relations. -/
def Mono (F : Rel α β → Rel α β) : Prop :=
  ∀ ⦃S S' : Rel α β⦄, le S S' → le (F S) (F S')

/-- Impredicative least pre-fixpoint of `F`. -/
def lfp (F : Rel α β → Rel α β) : Rel α β :=
  fun a b => ∀ S : Rel α β, (∀ x y, F S x y → S x y) → S a b

/-- `lfp F` is contained in any prefixed point of `F`. -/
theorem lfp_le_of_prefixed {F : Rel α β → Rel α β} {S : Rel α β}
    (h : le (F S) S) : le (lfp F) S :=
  fun _ _ hlfp => hlfp S h

/-- `lfp F` is itself a prefixed point of `F` (assuming monotonicity). -/
theorem lfp_prefixed {F : Rel α β → Rel α β} (hmono : Mono F) :
    le (F (lfp F)) (lfp F) := by
  intro a b hF S hS
  have hsub : le (lfp F) S := lfp_le_of_prefixed hS
  exact hS a b (hmono hsub a b hF)

/-- `lfp F` is also a postfixed point of `F` (assuming monotonicity). -/
theorem lfp_postfixed {F : Rel α β → Rel α β} (hmono : Mono F) :
    le (lfp F) (F (lfp F)) := by
  intro a b hlfp
  have hpre : le (F (F (lfp F))) (F (lfp F)) := hmono (lfp_prefixed hmono)
  exact hlfp _ hpre

/-- Knaster-Tarski unfolding for `lfp` under monotonicity. -/
theorem lfp_unfold {F : Rel α β → Rel α β} (hmono : Mono F) (a : α) (b : β) :
    lfp F a b ↔ F (lfp F) a b :=
  ⟨lfp_postfixed hmono a b, lfp_prefixed hmono a b⟩

/-- Pointwise extension order on environments: constants/unary/binary operators
are fixed, while uninterpreted predicate interpretations may grow. -/
def Env.le (ρ ρ' : Env) : Prop :=
  ρ.consts = ρ'.consts ∧ ρ.unary = ρ'.unary ∧ ρ.binary = ρ'.binary ∧
  (∀ τ name a, ρ.unaryRel τ name a → ρ'.unaryRel τ name a) ∧
  ∀ τ₁ τ₂ name a b, ρ.binaryRel τ₁ τ₂ name a b → ρ'.binaryRel τ₁ τ₂ name a b

theorem Env.le.refl (ρ : Env) : Env.le ρ ρ :=
  ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem Env.le.updateConst {ρ ρ' : Env} (h : Env.le ρ ρ')
    (τ : Srt) (x : String) (v : τ.denote) :
    Env.le (ρ.updateConst τ x v) (ρ'.updateConst τ x v) := by
  refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  simp only [Env.updateConst, h.1]

/-- Term evaluation only depends on `consts`, `unary`, and `binary`, so it is
invariant under `Env.le`. -/
theorem Term.eval_le {τ : Srt} {ρ ρ' : Env} (h : Env.le ρ ρ') (t : Term τ) :
    t.eval ρ = t.eval ρ' := by
  induction t with
  | var τ y => simp [Term.eval, Env.lookupConst, h.1]
  | const c =>
    cases c <;> simp [Term.eval, Const.denote, h.1]
  | unop op a iha =>
    simp only [Term.eval]; rw [iha]
    cases op <;> simp [UnOp.eval, h.2.1]
  | binop op a b iha ihb =>
    simp only [Term.eval]; rw [iha, ihb]
    cases op <;> simp [BinOp.eval, h.2.2.1]
  | ite c t e ihc iht ihe =>
    simp only [Term.eval]; rw [ihc, iht, ihe]

end Fix

/-! ## Unary least fixpoints

Pointwise least fixpoints on unary predicates. The relational `Fix` development
above could in principle be derived from this unary case at the pair sort
`α × β → Prop`; for now the two are kept as parallel constructions.

TODO: derive `Fix` (binary, on `α × β → Prop`) as an instance of `UnaryFix`
at the pair sort, instead of duplicating the development.
-/

namespace UnaryFix

/-- Pointwise inclusion of unary predicates. -/
def le {α : Type} (P Q : α → Prop) : Prop :=
  ∀ x, P x → Q x

/-- Monotone operator on unary predicates. -/
def Mono {α : Type} (F : (α → Prop) → α → Prop) : Prop :=
  ∀ ⦃P Q⦄, le P Q → le (F P) (F Q)

/-- Impredicative least pre-fixpoint of a unary predicate transformer. -/
def lfp {α : Type} (F : (α → Prop) → α → Prop) : α → Prop :=
  fun x => ∀ P : α → Prop, (∀ y, F P y → P y) → P x

/-- The least fixpoint is contained in every pre-fixpoint. -/
theorem lfp_le_of_prefixed {α : Type} {F : (α → Prop) → α → Prop}
    {P : α → Prop} (h : le (F P) P) : le (lfp F) P :=
  fun _ hlfp => hlfp P h

/-- The least fixpoint is a pre-fixpoint for monotone operators. -/
theorem lfp_prefixed {α : Type} {F : (α → Prop) → α → Prop}
    (hmono : Mono F) : le (F (lfp F)) (lfp F) := by
  intro x hF P hP
  have hsub : le (lfp F) P := lfp_le_of_prefixed hP
  exact hP x (hmono hsub x hF)

/-- The least fixpoint is a post-fixpoint for monotone operators. -/
theorem lfp_postfixed {α : Type} {F : (α → Prop) → α → Prop}
    (hmono : Mono F) : le (lfp F) (F (lfp F)) := by
  intro x hlfp
  have hpre : le (F (F (lfp F))) (F (lfp F)) := hmono (lfp_prefixed hmono)
  exact hlfp _ hpre

/-- Unfolding principle for unary least fixpoints. -/
theorem lfp_unfold {α : Type} {F : (α → Prop) → α → Prop}
    (hmono : Mono F) (x : α) :
    lfp F x ↔ F (lfp F) x :=
  ⟨lfp_postfixed hmono x, lfp_prefixed hmono x⟩

end UnaryFix

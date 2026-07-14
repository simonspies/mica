-- SUMMARY: Impredicative least fixpoints of monotone predicate and relation transformers.

/-! # Least fixpoints

`PredicateFix`, on transformers of `α → Prop`, is primitive. `RelationFix`, on
transformers of `α → β → Prop`, is derived from it at the pair sort `α × β`. -/

namespace PredicateFix

/-- Pointwise inclusion of predicates. -/
def le {α : Type} (P Q : α → Prop) : Prop :=
  ∀ x, P x → Q x

/-- Monotone operator on predicates. -/
def Mono {α : Type} (F : (α → Prop) → α → Prop) : Prop :=
  ∀ ⦃P Q⦄, le P Q → le (F P) (F Q)

/-- Impredicative least pre-fixpoint of a predicate transformer. -/
def lfp {α : Type} (F : (α → Prop) → α → Prop) : α → Prop :=
  fun x => ∀ P : α → Prop, (∀ y, F P y → P y) → P x

/-- The least fixpoint is contained in every pre-fixpoint. -/
theorem lfp_le_of_prefixed {α : Type} {F : (α → Prop) → α → Prop}
    {P : α → Prop} (h : le (F P) P) : le (lfp F) P :=
  fun _ hlfp => hlfp P h

/-- The least fixpoint is a pre-fixpoint for monotone operators. -/
private theorem lfp_prefixed {α : Type} {F : (α → Prop) → α → Prop}
    (hmono : Mono F) : le (F (lfp F)) (lfp F) := by
  intro x hF P hP
  have hsub : le (lfp F) P := lfp_le_of_prefixed hP
  exact hP x (hmono hsub x hF)

/-- The least fixpoint is a post-fixpoint for monotone operators. -/
private theorem lfp_postfixed {α : Type} {F : (α → Prop) → α → Prop}
    (hmono : Mono F) : le (lfp F) (F (lfp F)) := by
  intro x hlfp
  have hpre : le (F (F (lfp F))) (F (lfp F)) := hmono (lfp_prefixed hmono)
  exact hlfp _ hpre

/-- Unfolding principle for least fixpoints of predicate transformers. -/
theorem lfp_unfold {α : Type} {F : (α → Prop) → α → Prop}
    (hmono : Mono F) (x : α) :
    lfp F x ↔ F (lfp F) x :=
  ⟨lfp_postfixed hmono x, lfp_prefixed hmono x⟩

end PredicateFix

namespace RelationFix

/-- A binary relation between `α` and `β`. -/
abbrev Rel (α β : Type) := α → β → Prop

/-- Pointwise inclusion of relations. -/
def le (R S : Rel α β) : Prop := ∀ a b, R a b → S a b

/-- Monotone operator on relations. -/
def Mono (F : Rel α β → Rel α β) : Prop :=
  ∀ ⦃S S' : Rel α β⦄, le S S' → le (F S) (F S')

/-- A relation transformer viewed as a predicate transformer on pairs. -/
private def paired (F : Rel α β → Rel α β) : (α × β → Prop) → α × β → Prop :=
  fun P p => F (fun a b => P (a, b)) p.1 p.2

/-- Least pre-fixpoint of a relation transformer, taken at the pair sort. -/
def lfp (F : Rel α β → Rel α β) : Rel α β :=
  fun a b => PredicateFix.lfp (paired F) (a, b)

private theorem paired_mono {F : Rel α β → Rel α β} (hmono : Mono F) : PredicateFix.Mono (paired F) :=
  fun _ _ hPQ p hF => hmono (fun a b hab => hPQ (a, b) hab) p.1 p.2 hF

/-- `lfp F` is contained in any prefixed point of `F`. -/
theorem lfp_le_of_prefixed {F : Rel α β → Rel α β} {S : Rel α β}
    (h : le (F S) S) : le (lfp F) S :=
  fun a b hlfp =>
    PredicateFix.lfp_le_of_prefixed (P := fun p => S p.1 p.2)
      (fun p hp => h p.1 p.2 hp) (a, b) hlfp

/-- `lfp F` is itself a prefixed point of `F` (assuming monotonicity). -/
theorem lfp_prefixed {F : Rel α β → Rel α β} (hmono : Mono F) :
    le (F (lfp F)) (lfp F) :=
  fun a b hF => PredicateFix.lfp_prefixed (paired_mono hmono) (a, b) hF

/-- `lfp F` is also a postfixed point of `F` (assuming monotonicity). -/
private theorem lfp_postfixed {F : Rel α β → Rel α β} (hmono : Mono F) :
    le (lfp F) (F (lfp F)) :=
  fun a b hlfp => PredicateFix.lfp_postfixed (paired_mono hmono) (a, b) hlfp

/-- Knaster-Tarski unfolding for `lfp` under monotonicity. -/
theorem lfp_unfold {F : Rel α β → Rel α β} (hmono : Mono F) (a : α) (b : β) :
    lfp F a b ↔ F (lfp F) a b :=
  ⟨lfp_postfixed hmono a b, lfp_prefixed hmono a b⟩

end RelationFix

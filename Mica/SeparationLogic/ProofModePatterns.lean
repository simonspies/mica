-- SUMMARY: Worked examples of Iris proof mode patterns used in the project.
import Mica.SeparationLogic.Axioms

/-! # Iris Proof Mode — Tactic Patterns

A playground / cheat-sheet illustrating how to use the Iris proof mode tactics
in Lean. Each section demonstrates a specific tactic or pattern with minimal
self-contained examples using our project's `iProp`.

See also `docs/iris-tactics.md` for a prose reference.
-/

open Iris Iris.BI

-- We work with `iProp` from `Axioms.lean` throughout.

/-! ## 1. Entering proof mode: `istart` / `istop` -/

/-- `istart` enters proof mode. The goal must be an entailment `P ⊢ Q`. -/
example (P : iProp) : P ⊢ P := by
  istart
  iintro HP
  iexact HP

/-! ## 2. Introduction: `iintro`

`iintro` introduces hypotheses from wands, implications, and quantifiers.
-/

/-- Introduce a single spatial hypothesis. -/
example (P Q : iProp) : P ∗ Q ⊢ P ∗ Q := by
  istart
  iintro H
  iexact H

/-- Introduce a universally quantified variable with `%x`. -/
example : ⊢ (∀ (n : Nat), ⌜n = n⌝ : iProp) := by
  istart
  iintro %n
  ipure_intro
  rfl

/-- Introduce a wand premise. -/
example (P Q : iProp) : P ⊢ (P -∗ Q) -∗ Q := by
  istart
  iintro HP Hwand
  iapply Hwand
  iexact HP

/-- Introduce multiple things in sequence. -/
example (P Q : iProp) : ⊢ ∀ (_n : Nat), P -∗ Q -∗ Q := by
  istart
  iintro %_n _HP HQ
  iexact HQ


/-! ## 3. Destructuring patterns

Patterns compose: `⟨H1, H2⟩` for `∗`/`∧`, `(H1 | H2)` for `∨`,
`%x` for quantified variables, `⌜h⌝` for pure propositions.
-/

/-- Destruct a separating conjunction on introduction. -/
example (P Q : iProp) : P ∗ Q ⊢ Q ∗ P := by
  istart
  iintro ⟨HP, HQ⟩
  isplitl [HQ]
  · iexact HQ
  · iexact HP

/-- Destruct a triple separating conjunction. -/
example (P Q R : iProp) : P ∗ Q ∗ R ⊢ R := by
  istart
  iintro ⟨_HP, _HQ, HR⟩
  iexact HR

/-- Destruct pure + spatial: `%` for pure, name for spatial. -/
example (P : iProp) (φ : Prop) : ⌜φ⌝ ∗ P ⊢ P := by
  istart
  iintro ⟨%_hpure, HP⟩
  iexact HP

/-- Nested pattern: conjunction inside conjunction. -/
example (P Q R S : iProp) : (P ∗ Q) ∗ (R ∗ S) ⊢ Q ∗ R := by
  istart
  iintro ⟨⟨_HP, HQ⟩, HR, _HS⟩
  isplitr [HR]
  · iexact HQ
  · iexact HR


/-! ## 4. Destructuring existing hypotheses: `icases`

`icases` destructs an hypothesis already in the context (unlike `iintro`
which destructs while introducing).
-/

/-- Split an existing hypothesis. -/
example (P Q : iProp) : P ∗ Q ⊢ Q ∗ P := by
  istart
  iintro H
  icases H with ⟨HP, HQ⟩
  isplitl [HQ]
  · iexact HQ
  · iexact HP

/-- Destruct a disjunction — creates two goals. -/
example (P Q R : iProp) : (P ∨ Q) ∗ R ⊢ R := by
  istart
  iintro ⟨(HP | HQ), HR⟩
  · iexact HR
  · iexact HR

/-- Destruct an existential. -/
example (P : Nat → iProp) : (∃ n, P n) ⊢ ∃ n, P n := by
  istart
  iintro ⟨%n, HP⟩
  iexists n
  iexact HP


/-! ## 5. Splitting separating conjunctions: `isplitr` / `isplitl`

The key difference from standard `constructor`:
- Spatial hypotheses must be *distributed* between the two subgoals.
- `isplitr` sends all spatial hypotheses to the **right** subgoal.
- `isplitl` sends all spatial hypotheses to the **left** subgoal.
- Bracket variants give fine-grained control.
-/

/-- `isplitr`: left goal gets no spatial hypotheses, right gets all. -/
example (P Q : iProp) : P ∗ Q ⊢ ⌜True⌝ ∗ (P ∗ Q) := by
  istart
  iintro H
  isplitr
  · ipure_intro; trivial   -- no spatial hyps needed
  · iexact H               -- H is here

/-- `isplitl`: left goal gets all spatial hypotheses. -/
example (P Q : iProp) : P ∗ Q ⊢ (P ∗ Q) ∗ ⌜True⌝ := by
  istart
  iintro H
  isplitl
  · iexact H
  · ipure_intro; trivial

/-- Bracket variant: distribute specific hypotheses. -/
example (P Q : iProp) : P ∗ Q ⊢ P ∗ Q := by
  istart
  iintro ⟨HP, HQ⟩
  isplitl [HP]         -- HP goes left, HQ goes right
  · iexact HP
  · iexact HQ

/-- Non-separating conjunction uses `isplit` (both sides get full context). -/
example (P : iProp) : P ⊢ P ∧ P := by
  istart
  iintro HP
  isplit
  · iexact HP
  · iexact HP


/-! ## 6. Existentials: `iexists` -/

/-- Provide a witness for an existential in the goal. -/
example (P : Nat → iProp) : P 42 ⊢ ∃ n, P n := by
  istart
  iintro HP
  iexists 42
  iexact HP

/-- Multiple witnesses in sequence. -/
example (P : Nat → Nat → iProp) : P 1 2 ⊢ ∃ a b, P a b := by
  istart
  iintro HP
  iexists 1, 2
  iexact HP


/-! ## 7. Pure reasoning: `ipure_intro` / `%` pattern -/

/-- `ipure_intro` turns a `⌜φ⌝` goal into a Lean goal. -/
example : ⊢ (⌜(1 : Nat) + 1 = 2⌝ : iProp) := by
  istart
  ipure_intro
  rfl

/-- Extracting a pure hypothesis with `%` in intro patterns. -/
example (P : iProp) : ⌜True⌝ ∗ P ⊢ P := by
  istart
  iintro ⟨%_, HP⟩
  iexact HP


/-! ## 8. Application: `iapply` -/

/-- Apply a wand hypothesis to the goal. -/
example (P Q : iProp) : P ∗ (P -∗ Q) ⊢ Q := by
  istart
  iintro ⟨HP, Hwand⟩
  iapply Hwand
  iexact HP

/-- Apply an external lemma. The lemma must conclude with an entailment. -/
example (v : Runtime.Val) (Q : Runtime.Val → iProp) : Q v ⊢ wp (.val v) Q := by
  istart
  iintro HQ
  iapply wp.val
  iexact HQ


/-! ## 9. Specialization: `ispecialize` -/

/-- Specialize a universal with a pure term via `%`. -/
example (P : Nat → iProp) : (∀ n, P n) ⊢ P 42 := by
  istart
  iintro Hall
  ispecialize Hall $$ %42
  iexact Hall

/-! ## 10. Persistency -/

/-- Introduce a persistent assertion, cross a persistency modality, and use it twice. -/
example (R Q : iProp): R ∗ □ Q ⊢ □ (Q ∗ Q) := by
  iintro ⟨HR, □HQ⟩
  imodintro
  isplitl
  . iexact HQ
  . iexact HQ


/-! ## 11. Hypothesis management -/

/-- `irevert` moves a hypothesis back into the goal as a wand. -/
example (P Q : iProp) : P ∗ Q ⊢ Q ∗ P := by
  istart
  iintro ⟨HP, HQ⟩
  irevert HP
  -- goal is now: Q ⊢ P -∗ Q ∗ P
  iintro HP
  isplitl [HQ]
  · iexact HQ
  · iexact HP


/-! ## 12. Combining Iris and Lean reasoning

Often the best approach is to use Lean term mode for simple entailment chains
and only enter proof mode for the parts that need hypothesis management.
-/

/-- Term-mode composition of entailments (no proof mode needed). -/
example (P Q R : iProp) (h1 : P ⊢ Q) (h2 : Q ⊢ R) : P ⊢ R :=
  h1.trans h2

/-- `sep_mono` for congruence under `∗`. -/
example (P P' Q Q' : iProp) (hp : P ⊢ P') (hq : Q ⊢ Q') : P ∗ Q ⊢ P' ∗ Q' :=
  sep_mono hp hq

/-- Mixing: enter proof mode only for the hard part. -/
example (P Q : iProp) : P ∗ Q ⊢ Q ∗ P := by
  istart
  iintro ⟨HP, HQ⟩
  isplitl [HQ]
  · iexact HQ
  · iexact HP

/-- Same thing purely in term mode using `sep_comm`. -/
example (P Q : iProp) : P ∗ Q ⊢ Q ∗ P :=
  sep_comm.1

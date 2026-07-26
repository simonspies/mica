-- SUMMARY: Assertion data for specifications: atoms, the assertion language, predicate transformers, and specs.
import Mica.SourceTinyML.Types
import Mica.FOL.Formulas

/-!
# Assertion data

The data of the assertion language a specification elaborates into: `Atom`,
`Assertion`, `PredTrans`, and `Spec`. Everything here needs only `TinyML.Typ`
and the FOL term/formula language, so it sits *below* typing, which is what lets
elaboration produce a `Spec` in a single walk.

Operations, semantic interpretations, and proofs stay in the verifier:
`Verifier/Atoms.lean`, `Verifier/Assertions.lean`,
`Verifier/PredicateTransformers.lean`, and `Verifier/Specifications.lean`.
-/

-- ---------------------------------------------------------------------------
-- Atoms
-- ---------------------------------------------------------------------------

/-- A sort predicate: asserts that a value-sorted term has a specific sort,
    and extracts the underlying typed value. -/
inductive Atom : Srt → Type where
  | isint  : Term .value → Atom .int
  | isbool : Term .value → Atom .bool
  | isinj  (tag : Nat) (arity : Nat) : Term .value → Atom .value
  | own    : Term .value → TinyML.Typ → Atom .value
  | arr : Term .value → TinyML.Typ → Atom .value
  | rel    (name : String) : Term .value → Atom .value
  deriving DecidableEq

-- ---------------------------------------------------------------------------
-- Assertions
-- ---------------------------------------------------------------------------

inductive Assertion : Type → Type where
  | ret    : α → Assertion α
  | assert : Formula → Assertion α → Assertion α
  | let_   : (v : Var) → Term v.sort → Assertion α → Assertion α
  | pred   : (v : Var) → Atom v.sort → Assertion α → Assertion α
  | ite    : Formula → Assertion α → Assertion α → Assertion α

private def Assertion.decideEq [DecidableEq α] : (a b : Assertion α) → Decidable (a = b)
  | .ret a, .ret b => match decEq a b with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .assert φ₁ k₁, .assert φ₂ k₂ => match decEq φ₁ φ₂, k₁.decideEq k₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by subst h₁; subst h₂; rfl)
    | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .let_ v₁ t₁ k₁, .let_ v₂ t₂ k₂ => match decEq v₁ v₂ with
    | isTrue hv => by
        subst hv
        exact match decEq t₁ t₂, k₁.decideEq k₂ with
          | isTrue ht, isTrue hk => isTrue (by subst ht; subst hk; rfl)
          | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
          | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .pred v₁ p₁ k₁, .pred v₂ p₂ k₂ => match decEq v₁ v₂ with
    | isTrue hv => by
        subst hv
        exact match decEq p₁ p₂, k₁.decideEq k₂ with
          | isTrue hp, isTrue hk => isTrue (by subst hp; subst hk; rfl)
          | isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
          | _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .ite φ₁ kt₁ ke₁, .ite φ₂ kt₂ ke₂ =>
    match decEq φ₁ φ₂, kt₁.decideEq kt₂, ke₁.decideEq ke₂ with
    | isTrue hφ, isTrue ht, isTrue he => isTrue (by subst hφ; subst ht; subst he; rfl)
    | isFalse h, _, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, isFalse h, _ => isFalse (by intro heq; cases heq; exact h rfl)
    | _, _, isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .ret _, .assert .. | .ret _, .let_ .. | .ret _, .pred .. | .ret _, .ite ..
  | .assert .., .ret _ | .assert .., .let_ .. | .assert .., .pred .. | .assert .., .ite ..
  | .let_ .., .ret _ | .let_ .., .assert .. | .let_ .., .pred .. | .let_ .., .ite ..
  | .pred .., .ret _ | .pred .., .assert .. | .pred .., .let_ .. | .pred .., .ite ..
  | .ite .., .ret _ | .ite .., .assert .. | .ite .., .let_ .. | .ite .., .pred .. =>
    isFalse (by intro h; cases h)

instance [DecidableEq α] : DecidableEq (Assertion α) := Assertion.decideEq

-- ---------------------------------------------------------------------------
-- Predicate transformers
-- ---------------------------------------------------------------------------

def PredTrans := Assertion (Pred (Assertion Unit))

instance : DecidableEq PredTrans := by
  unfold PredTrans Pred
  infer_instance

-- ---------------------------------------------------------------------------
-- Specifications
-- ---------------------------------------------------------------------------

/-- A complete specification for a (possibly multi-argument) function, pairing the
    predicate transformer with the argument and return types from the function annotation. -/
structure Spec where
  args    : List (String × TinyML.Typ)
  retTy   : TinyML.Typ
  pred    : PredTrans
  deriving DecidableEq

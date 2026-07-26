-- SUMMARY: Data of atoms, assertions, and completed specifications, parametric in the type language they mention.
import Mica.FOL.Formulas

/-!
# Assertion data

The syntax of verifier atoms, assertions, and completed specifications,
separated from their semantics and from the verifier operations on them
(`Mica/Verifier/Atoms.lean`, `Mica/Verifier/Assertions.lean`,
`Mica/Verifier/Specifications.lean`).

Everything here is parametric in the type language `T` that atoms mention;
the verifier instantiates `T := TinyML.Typ`. The parameter exists because a
TinyML function type carries the specification of the function it describes,
so `TinyML.Typ` is defined by nesting the types below and cannot be defined
before them.

For the same reason `Post` is a named structure rather than a pair: a nested
inductive may not occur inside its own type parameter, so the payload of the
outer assertion has to be a type constructor other than `Assertion` itself.
-/

/-- A sort predicate: asserts that a value-sorted term has a specific sort,
    and extracts the underlying typed value. -/
inductive Atom (T : Type) : Srt → Type where
  | isint  : Term .value → Atom T .int
  | isbool : Term .value → Atom T .bool
  | isinj  (tag : Nat) (arity : Nat) : Term .value → Atom T .value
  | own    : Term .value → T → Atom T .value
  | arr : Term .value → T → Atom T .value
  | rel    (name : String) : Term .value → Atom T .value
  deriving DecidableEq

/-- An assertion: a sequence of assumptions, bindings, and case splits ending
    in a value of type `α`. -/
inductive Assertion (T : Type) : Type → Type where
  | ret    : α → Assertion T α
  | assert : Formula → Assertion T α → Assertion T α
  | let_   : (v : Var) → Term v.sort → Assertion T α → Assertion T α
  | pred   : (v : Var) → Atom T v.sort → Assertion T α → Assertion T α
  | ite    : Formula → Assertion T α → Assertion T α → Assertion T α

/-- The postcondition of a predicate transformer: the name bound to the result
    value, together with the assertion that must hold of it. -/
structure Post (T : Type) where
  name : String
  body : Assertion T Unit

/-- A predicate transformer: an assertion establishing the precondition and
    ending in the postcondition the result must satisfy.

    `Spec.pred` spells this type out rather than naming it: `Typ` nests `Spec`,
    and the nested-inductive elaborator does not unfold definitions. -/
def PredTrans (T : Type) := Assertion T (Post T)

/-- A complete specification for a (possibly multi-argument) function: the
    argument names and the predicate transformer describing its behavior. The
    argument and result *types* live in the enclosing n-ary arrow, not here. -/
structure Spec (T : Type) where
  args : List String
  pred : Assertion T (Post T)

/-- Specifications print as a placeholder. -/
instance : Repr (Spec T) := ⟨fun _ _ => "<spec>"⟩

-- ---------------------------------------------------------------------------
-- Decidable equality
-- ---------------------------------------------------------------------------

private def Assertion.decideEq [DecidableEq T] [DecidableEq α] :
    (a b : Assertion T α) → Decidable (a = b)
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

instance [DecidableEq T] [DecidableEq α] : DecidableEq (Assertion T α) := Assertion.decideEq

deriving instance DecidableEq for Post

instance [DecidableEq T] : DecidableEq (PredTrans T) := by
  unfold PredTrans; infer_instance

deriving instance DecidableEq for Spec

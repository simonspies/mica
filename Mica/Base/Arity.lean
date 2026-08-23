-- SUMMARY: Intrinsic arities and the argument tuples indexed by them.

/-! # Arity

An `Arity` is the number of arguments of a built-in operation. `Arity.tup`
is the shape of a tuple of that many arguments. The intrinsic registry and
the relational encoder both index their arguments by this type. Therefore it
is below both of them.
-/

/-- The arity of an intrinsic. Add more cases if you need them. -/
inductive Arity
  | zero
  | one
  | two
  | three
  deriving DecidableEq, Repr

/-- The number of arguments of an `Arity`. -/
def Arity.toNat : Arity → Nat
  | .zero => 0
  | .one  => 1
  | .two  => 2
  | .three => 3

/-- The type of a tuple of `n` elements of type `α`. -/
abbrev Arity.tup : Arity → Type → Type
  | .zero, _ => Unit
  | .one,  α => α
  | .two,  α => α × α
  | .three, α => α × α × α

/-- `p` is true of each element of the tuple. -/
def Arity.All {α : Type} (p : α → Prop) : (n : Arity) → Arity.tup n α → Prop
  | .zero, _ => True
  | .one, a => p a
  | .two, (a, b) => p a ∧ p b
  | .three, (a, b, c) => p a ∧ p b ∧ p c

/-- Apply `f` to each element of the tuple. -/
def Arity.map {α β : Type} (f : α → β) : (n : Arity) → Arity.tup n α → Arity.tup n β
  | .zero, _ => ()
  | .one, a => f a
  | .two, (a, b) => (f a, f b)
  | .three, (a, b, c) => (f a, f b, f c)

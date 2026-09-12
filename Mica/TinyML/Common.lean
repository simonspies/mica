-- SUMMARY: Common TinyML vocabulary for variables, primitive operators, and constants.
/-! # Common vocabulary shared across all TinyML IRs: variables, operators, constants. -/

namespace TinyML

abbrev Var := String

/-- Whether code runs, or exists only for the verifier. Ghost code is deleted
before compilation, so it may not touch the heap and nothing that runs may
depend on it. -/
inductive Mode where
  | runtime
  | ghost
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Whether a spec-level function's defining equation reaches the solver
context. An opaque one goes out through its unfolding function instead. -/
inductive Transparency where
  | transparent
  | opaque
  deriving Repr, Inhabited, BEq, DecidableEq

/-- What `[@@fn]` records. The name is the one the spec-level symbols take. -/
structure Relation where
  name : Var
  ghost : Bool := false
  transparency : Transparency := .transparent
  deriving Repr, Inhabited, BEq, DecidableEq

/-- The ghost function an opaque `[@@fn]` publishes. -/
def Relation.unfoldName (r : Relation) : Var := r.name ++ "_unfold"

/-- Whether a mutable allocation is owned directly or shared through an invariant. -/
inductive Ownership where
  | owned
  | shared
  deriving Repr, BEq, Inhabited, DecidableEq

inductive BinOp where
  | add | sub | mul | div | mod
  | eq | lt | le | gt | ge
  | and | or
  deriving Repr, BEq, Inhabited, DecidableEq

inductive UnOp where
  | neg | not
  | proj (n : Nat)
  deriving Repr, BEq, Inhabited, DecidableEq

inductive Const where
  | int  (n : Int)
  | int32 (bits : BitVec 32)
  | int64 (bits : BitVec 64)
  | bool (b : Bool)
  | char (c : UInt8)
  | string (s : List UInt8)
  | float (bits : UInt64)
  | unit
  deriving Repr, BEq, DecidableEq

end TinyML

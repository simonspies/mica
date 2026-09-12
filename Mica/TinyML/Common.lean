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

/-- What `[@@fn]` records: the name the spec-level symbols take, and whether
ghost code can call the function. -/
structure Relation where
  name : Var
  ghost : Bool := false
  deriving Repr, Inhabited, BEq, DecidableEq

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

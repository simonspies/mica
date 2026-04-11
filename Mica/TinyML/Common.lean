/-! # Common vocabulary shared across all TinyML IRs: variables, operators, constants. -/

namespace TinyML

abbrev Var := String

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
  | bool (b : Bool)
  | unit
  deriving Repr, BEq, DecidableEq

end TinyML

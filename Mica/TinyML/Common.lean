-- SUMMARY: Common TinyML vocabulary for variables, primitive operators, and constants.
/-! # Common vocabulary shared across all TinyML IRs: variables, operators, constants. -/

namespace TinyML

abbrev Var := String

structure DeclMeta (S : Type) where
  spec : Option S := none
  relation : Option String := none
  deriving Repr, BEq, Inhabited

def DeclMeta.mapSpec {S T : Type} (f : S -> Option T) (m : DeclMeta S) : DeclMeta T :=
  { spec := m.spec.bind f, relation := m.relation }

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
  | char (c : UInt8)
  | string (s : List UInt8)
  | float (bits : UInt64)
  | unit
  deriving Repr, BEq, DecidableEq

end TinyML

-- SUMMARY: Untyped abstract syntax for specifications embedded in frontend programs.
/-!
# Specification Language

Untyped AST for the specification language. Specs are written as OCaml
expressions in `[@@spec ...]` attributes, parsed into TinyML, then
converted to this AST by `SpecParser`. The sort-checking translation
to typed `Assertion`/`Term`/`Formula` values lives in
`Verifier/SpecTranslation.lean`.
-/

namespace Spec

inductive BinOp where
  | add | sub | mul | div | mod
  | eq | lt | le | gt | ge
  | and | or
  deriving Repr, BEq, Inhabited

inductive UnOp where
  | neg | not
  | tagof | arityof | payloadof
  | proj (n : Nat)
  | inj (tag arity : Nat)
  deriving Repr, BEq, Inhabited

mutual
  inductive Term where
    | var (name : String)
    | int (n : Int)
    | bool (b : Bool)
    | unit
    | binop (op : BinOp) (lhs rhs : Term)
    | unop (op : UnOp) (arg : Term)
    | tuple (es : List Term)
    | ite (cond thn els : Term)
    deriving Repr, BEq, Inhabited
end

inductive Pred where
  | isint (arg : Term)
  | isbool (arg : Term)
  | isinj (tag arity : Nat) (arg : Term)
  | own (loc : Term)
  deriving Repr, BEq, Inhabited

inductive Assert (α : Type) where
  | ret (val : α)
  | assert (cond : Term) (rest : Assert α)
  | let_ (name : String) (val : Term) (rest : Assert α)
  | bind (pred : Pred) (name : String) (rest : Assert α)
  | ite (cond : Term) (thn els : Assert α)
  deriving Repr, BEq, Inhabited

abbrev Post := Assert Unit
abbrev Pre := Assert (String × Post)
abbrev Body := List String × Pre

end Spec

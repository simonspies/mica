-- SUMMARY: Abstract syntax for specifications embedded in TinyML programs.
import Mica.TinyML.Untyped
import Mica.TinyML.Typed
/-!
# Specification Language

Abstract syntax for `[@@spec ...]` attributes. `SpecParser` recognises the
control structure (`assert`, `let`, predicate `bind`, `ite`, `ret`) and keeps
the embedded leaf expressions as ordinary TinyML, parametric in their type `ε`:
`Untyped.Expr` before typechecking, `Typed.Expr` after. Typechecking happens
during elaboration (`Typing.lean`); the FOL translation lives in
`Verifier/SpecTranslation.lean`.
-/

namespace Spec

/-- Specification predicates. Each names a spec-level variable already in
scope, whose encoded value the translator looks up directly. -/
inductive Pred where
  | isinj (tag arity : Nat) (scrut : String)
  | own (loc : String)
  /-- Ownership of a mutable array `loc`, binding its vector snapshot. -/
  | arr (loc : String)
  deriving Inhabited

/-- The assertion language, parametric in the embedded leaf expression type `ε`
(used by `assert`, `let_`, and `ite`). -/
inductive Assert (ε α : Type) where
  | ret (val : α)
  | assert (cond : ε) (rest : Assert ε α)
  | let_ (name : String) (val : ε) (rest : Assert ε α)
  | bind (p : Pred) (name : String) (ty : TinyML.Typ) (rest : Assert ε α)
  | ite (cond : ε) (thn els : Assert ε α)

instance [Inhabited α] : Inhabited (Assert ε α) := ⟨.ret default⟩

abbrev Post (ε : Type) := Assert ε Unit
abbrev Pre (ε : Type) := Assert ε (String × Post ε)

/-- A spec body: the bound argument names together with the precondition. -/
abbrev Body (ε : Type) := List String × Pre ε

end Spec

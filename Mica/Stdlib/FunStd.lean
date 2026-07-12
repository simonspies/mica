-- SUMMARY: `Fun.id`
import Mica.Stdlib.Combinators

open Iris Iris.BI

/-!
# Functions

The identity function as an example exercising the support for implementing
polymorphic intrinsics.

-/

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## `Fun.id` -/

def funIdDefAxiom : Formula :=
  .forall_ "x" .value [.term (unTerm "fun_id" (.var .value "x"))] <|
    .eq .value (unTerm "fun_id" (.var .value "x")) (.var .value "x")

/-- `Fun.id : 'a -> 'a`, the polymorphic identity. -/
def funIdB : Pure.Unary where
  name     := "fun_id"
  path     := some ("Fun", ["id"])
  arg      := .poly "a"
  res      := .poly "a"
  f        := (id : Runtime.Val → Runtime.Val)
  dom      := fun _ => True
  pre      := none
  defAxiom := funIdDefAxiom

def funId : Intrinsic := funIdB.toIntrinsic

@[simp] theorem funId_arity : funId.arity = .one := rfl
@[simp] theorem funId_folSym : funId.folSym = some funIdB.sym := rfl
@[simp] theorem funIdSym_name : funIdB.sym.name = "fun_id" := rfl

def funIdLawful : funIdB.Lawful where
  argL         := Embedding.lawfulPoly "a"
  resL         := Embedding.lawfulPoly "a"
  domSound     := fun _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ => .rfl
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; exact nomatch h
  defEval      := by
    intrinsic_def_eval [unTerm, funIdB, funIdDefAxiom]

instance : IntrinsicSound [funId] funId := funIdLawful.sound

end Intrinsics

end Stdlib

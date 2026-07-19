-- SUMMARY: Error intrinsics (`failwith`, `invalid_arg`): precondition `False`, so the verifier must prove every raise unreachable.
import Mica.Stdlib.Combinators

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## FOL symbols

Both symbols are uninterpreted and never constrained: the `False` precondition
means no verified program reaches a call, so no defining axiom is needed. -/

/-- FOL symbol for `failwith`; uninterpreted, never constrained. -/
def failwithSym : FOL.Symbol .one where
  name   := "failwith"
  interp := fun _ => .unit

/-- FOL symbol for `invalid_arg`; uninterpreted, never constrained. -/
def invalidArgSym : FOL.Symbol .one where
  name   := "invalid_arg"
  interp := fun _ => .unit

@[simp] theorem failwithSym_name : failwithSym.name = "failwith" := rfl
@[simp] theorem invalidArgSym_name : invalidArgSym.name = "invalid_arg" := rfl

/-! ## `failwith` -/

/-- `failwith : string -> empty` with precondition `False`: the call is only
    verifiable in a contradictory context, i.e. on a dead path. At runtime the
    reduce relation is empty (real OCaml raises). -/
def failwithB : Pure.Unary where
  name     := "failwith"
  path     := some ("failwith", [])
  arg      := .str
  res      := .empty
  f        := fun _ => ()
  dom      := fun _ => False
  pre      := some fun _ => .false_
  defAxiom := .true_

def failwith : Intrinsic := failwithB.toIntrinsic

@[simp] theorem failwith_arity : failwith.arity = .one := rfl
@[simp] theorem failwith_folSym : failwith.folSym = some failwithSym := rfl

def failwithLawful : failwithB.Lawful where
  argL         := Embedding.lawfulStr
  resL         := Embedding.lawfulEmpty
  domSound     := fun _ _ h => (h _ rfl).elim
  semWellTyped := fun _ _ _ hdom => hdom.elim
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := fun _ h => nomatch h
  defEval      := fun _ _ => trivial

instance : IntrinsicSound [failwith] failwith := failwithLawful.sound

/-! ## `invalid_arg` -/

/-- `invalid_arg : string -> empty` with precondition `False`; identical to
    `failwith` except for the exception it raises in real OCaml, which the
    verifier never observes. -/
def invalidArgB : Pure.Unary where
  name     := "invalid_arg"
  path     := some ("invalid_arg", [])
  arg      := .str
  res      := .empty
  f        := fun _ => ()
  dom      := fun _ => False
  pre      := some fun _ => .false_
  defAxiom := .true_

def invalidArg : Intrinsic := invalidArgB.toIntrinsic

@[simp] theorem invalidArg_arity : invalidArg.arity = .one := rfl
@[simp] theorem invalidArg_folSym : invalidArg.folSym = some invalidArgSym := rfl

def invalidArgLawful : invalidArgB.Lawful where
  argL         := Embedding.lawfulStr
  resL         := Embedding.lawfulEmpty
  domSound     := fun _ _ h => (h _ rfl).elim
  semWellTyped := fun _ _ _ hdom => hdom.elim
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := fun _ h => nomatch h
  defEval      := fun _ _ => trivial

instance : IntrinsicSound [invalidArg] invalidArg := invalidArgLawful.sound

end Intrinsics
end Stdlib

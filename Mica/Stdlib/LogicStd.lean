-- SUMMARY: Logical primitives for specifications only (`Logic.eq`): equality of values, with precondition `False` so that no program can call it.
import Mica.Stdlib.Combinators

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## `Logic.eq`

`Logic.eq : 'a -> 'a -> bool` is a primitive for specifications only. It is
the equality of the encoded values of its two arguments. It lets a
specification state an equality that the surface operator `=` refuses, for
example on a list, a tuple, or another cell that is not a scalar. The
verifier proves such an equality with one structural SMT equality.

`Logic.eq` is not one of the two runtime equalities of OCaml:

* It is not physical equality (`==`). Physical equality tells two lists apart
  by their addresses in the heap.
* It is not the structural equality `=` of OCaml. That equality follows
  pointers to any depth. It reads through a `ref` and through an array cell,
  and it compares the contents at that moment. It can also loop forever on a
  cycle.

`Logic.eq` is the equality of the encoded value. It is structural on the
immutable part of the value. A heap location is an atom, and two locations
are equal only if they are the same location. Therefore the equality does not
read through a reference, and it does not reduce a list to one pointer. On
the first-order immutable data that it is made for, such as
`(int * int) list`, it agrees with the `=` of OCaml.

No operation of OCaml has exactly this behaviour. Therefore there is nothing
to run. The precondition is `False`, so the verifier rejects every call in a
program as unreachable. The runtime relation is empty, like the relation of
`failwith`. -/

/-- The encoding of logical equality as a plain value term. It uses no
    quantifier. -/
def logicEqDirect : FOL.Direct .two where
  interp := fun (a, b) => .bool (decide (a = b))
  encode := fun (a, b) => .unop .ofBool (.binop .eq a b)
  wfIn := by
    intro Δ args hargs
    exact ⟨trivial, ⟨trivial, hargs.1, hargs.2⟩⟩
  eval := by intro ρ args; rcases args with ⟨a, b⟩; rfl

/-- `Logic.eq`: equality of values, for specifications only. The comment at
    the top of this section says which equality this is, and why no program
    can call it. -/
def logicEq : Intrinsic where
  arity := .two
  name := "logic_eq"
  path := some ("Logic", ["eq"])
  reduce := fun _ _ _ _ => False
  wp := fun _ _ => iprop(False)
  argTys := [.tvar "a", .tvar "a"]
  retTy := .bool
  spec :=
    { args := ["a", "b"]
      pred := .assert .false_ (.ret ⟨"ret", .ret ()⟩) }
  folTerm := some (.direct logicEqDirect)
  axioms := []

@[simp] theorem logicEq_arity : logicEq.arity = .two := rfl
@[simp] theorem logicEq_folSym : logicEq.folSym = none := rfl

/-- The intrinsic is sound, and it needs no other intrinsic to be sound. Both
    its specification and its weakest precondition are false, and it adds no
    axiom. -/
@[reducible] def logicEqSound : IntrinsicSound [] logicEq where
  argLen := rfl
  specWf := by
    intro Δ _ _
    simp [logicEq, Intrinsic.specArgs, PredTrans.wfIn, Assertion.wfIn]
    trivial
  bridge := by
    intro _ σ W vs ρ Φ _
    simp only [logicEq, PredTrans.apply, Assertion.pre]
    iintro H
    icases H with ⟨_, %hfalse, _⟩
    exact hfalse.elim
  wp_sound := by
    intro _ _ _ vs _
    match vs with
    | [] => exact false_elim
    | [_] => exact false_elim
    | [_, _] => exact false_elim
    | _ :: _ :: _ :: _ => exact false_elim
  axiomWf := by
    intro _ _ _ a ha
    cases ha
  proof := by
    intro _ _ a ha
    cases ha

instance : IntrinsicSound [] logicEq := logicEqSound

end Intrinsics
end Stdlib

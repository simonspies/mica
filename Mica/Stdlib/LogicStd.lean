-- SUMMARY: Spec-only logical primitives (`Logic.eq`): value equality usable in specs, with precondition `False` so it can never be called at runtime.
import Mica.Stdlib.Combinators

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## `Logic.eq`

`Logic.eq : 'a -> 'a -> bool` is a *specification-only* primitive: equality of
the two arguments' encoded values.  It exists so specifications can state
equality on values the surface `=` operator rejects — lists, tuples, and other
non-scalar cells — which the verifier reasons about with a single structural
SMT equality.

The equality it denotes is neither of OCaml's runtime equalities:

* It is **not** physical equality (`==`), which would distinguish two lists by
  their heap addresses.
* It is **not** OCaml's structural `=`, which follows pointers deeply — it
  dereferences `ref`s and array cells and compares their live contents (and can
  diverge on cycles).

It is equality of the *encoded value*: structural over the immutable value
structure, but a heap location is an atom compared by identity, so the equality
neither follows a reference into the heap nor collapses a whole list to one
pointer.  On the first-order immutable data it is meant for — e.g.
`(int * int) list` — it coincides with OCaml's `=`.

Because no OCaml operation implements exactly this, there is nothing to run:
the precondition is `False` (so the verifier rejects every runtime call as
unreachable) and the runtime facet is a `failwith`-style empty reduction. -/

/-- Quantifier-free encoding of logical equality as an ordinary value term. -/
def logicEqDirect : FOL.Direct .two where
  interp := fun (a, b) => .bool (decide (a = b))
  encode := fun (a, b) => .unop .ofBool (.binop .eq a b)
  wfIn := by
    intro Δ args hargs
    exact ⟨trivial, ⟨trivial, hargs.1, hargs.2⟩⟩
  eval := by intro ρ args; rcases args with ⟨a, b⟩; rfl

/-- `Logic.eq`: value equality, spec-only.  See the module comment for exactly
    which equality this is and why it cannot be run. -/
def logicEq : Intrinsic where
  arity := .two
  name := "logic_eq"
  path := some ("Logic", ["eq"])
  reduce := fun _ _ _ _ => False
  wp := fun _ _ => iprop(False)
  spec :=
    { args := [("a", .tvar "a"), ("b", .tvar "a")]
      retTy := .bool
      pred := .assert .false_ (.ret ("ret", .ret ())) }
  typing := schemeTyping [.tvar "a", .tvar "a"]
  folTerm := some (.direct logicEqDirect)
  axioms := []

@[simp] theorem logicEq_arity : logicEq.arity = .two := rfl
@[simp] theorem logicEq_folSym : logicEq.folSym = none := rfl

/-- A runtime-forbidden equality intrinsic is sound independently of any
    registry fragment: its callable specification and weakest precondition are
    both false, and it contributes no axioms. -/
@[reducible] def logicEqSound : IntrinsicSound [] logicEq where
  specWf := by
    intro Δ _ _
    simp [logicEq, Intrinsic.specArgs, PredTrans.wfIn, Assertion.wfIn]
    trivial
  bridge := by
    intro _ σ Θ vs ρ Φ _
    simp only [logicEq, Spec.instantiate, PredTrans.apply, Assertion.pre]
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

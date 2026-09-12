-- SUMMARY: Logical primitives for specifications only (`Logic.eq`, `Logic.size`): equality and structural size of values, with precondition `False` so that no program can call them.
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
def logicEqDirect : FOL.Direct .two :=
  fun (a, b) => .unop .ofBool (.binop .eq a b)

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
      ghost := []
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
  folWf := by
    rintro _ ⟨rfl⟩ Δ ⟨a, b⟩ hargs
    exact ⟨trivial, ⟨trivial, hargs.1, hargs.2⟩⟩

instance : IntrinsicSound [] logicEq := logicEqSound

/-! ## `Logic.size`

`Logic.size : 'a -> int` is a primitive for specifications only, like
`Logic.eq`: its precondition is `False`, so no program can call it. It counts
the constructor nodes of the encoded value, which gives a `[@@decreases]`
measure for a specification function that recurses into a constructor payload.

The axioms are the defining equations, each guarded by the recognizer of its
case, plus the lower bound `0 ≤ size v`, which the equations alone do not give
the solver because it needs induction. -/

mutual
/-- The number of constructor nodes in a value. -/
private def size : Runtime.Val → Int
  | .inj _ _ payload => 1 + size payload
  | .tuple vs => sizeTuple vs
  | _ => 0

/-- The number of constructor nodes in the components `vs` of a tuple. -/
private def sizeTuple : List Runtime.Val → Int
  | [] => 0
  | v :: vs => size v + sizeTuple vs
end

mutual
private theorem size_nonneg (v : Runtime.Val) : 0 ≤ size v := by
  cases v with
  | inj _ _ p => have := size_nonneg p; simp only [size]; omega
  | tuple vs => simpa only [size] using sizeTuple_nonneg vs
  | _ => simp [size]

private theorem sizeTuple_nonneg (vs : List Runtime.Val) : 0 ≤ sizeTuple vs := by
  cases vs with
  | nil => simp [sizeTuple]
  | cons v vs => have := size_nonneg v; have := sizeTuple_nonneg vs; simp only [sizeTuple]; omega
end

/-- The standard interpretation is total: every value has a size, not only a
    constructed one. -/
def logicSizeSym : FOL.Symbol .one where
  name   := "logic_size"
  interp := fun v => .int (size v)

@[simp] theorem logicSizeSym_name : logicSizeSym.name = "logic_size" := rfl

private def szTerm (t : Term .value) : Term .value := unTerm "logic_size" t
private def szInt (t : Term .value) : Term .int := .unop .toInt (szTerm t)

private def sizeVar : Term .value := .var .value "v"
private def sizeComponents : Term .vallist := .unop .toValList sizeVar

/-- Every axiom is triggered by the size term at the value it constrains. -/
private def sizeAxiom (body : Formula) : Axiom :=
  ⟨.forall_ "v" .value [.term (szTerm sizeVar)] body, .high⟩

private def logicSizeAxioms : List Axiom :=
  [ sizeAxiom (.unpred .isInt (szTerm sizeVar)),
    sizeAxiom (.binpred .le (.const (.i 0)) (szInt sizeVar)),
    sizeAxiom (.implies
      (.and (.not (.unpred .isOfInj sizeVar)) (.not (.unpred .isTuple sizeVar)))
      (.eq .int (szInt sizeVar) (.const (.i 0)))),
    sizeAxiom (.implies (.unpred .isOfInj sizeVar)
      (.eq .int (szInt sizeVar)
        (.binop .add (.const (.i 1)) (szInt (.unop .payloadOf sizeVar))))),
    sizeAxiom (.implies
      (.and (.unpred .isTuple sizeVar) (.eq .bool (.unop .visnil sizeComponents) (.const (.b true))))
      (.eq .int (szInt sizeVar) (.const (.i 0)))),
    sizeAxiom (.implies
      (.and (.unpred .isTuple sizeVar) (.eq .bool (.unop .visnil sizeComponents) (.const (.b false))))
      (.eq .int (szInt sizeVar)
        (.binop .add (szInt (.unop .vhead sizeComponents))
          (szInt (.unop .ofValList (.unop .vtail sizeComponents)))))) ]

def logicSize : Intrinsic where
  arity := .one
  name := "logic_size"
  path := some ("Logic", ["size"])
  reduce := fun _ _ _ _ => False
  wp := fun _ _ => iprop(False)
  argTys := [.tvar "a"]
  retTy := .int
  spec :=
    { args := ["a"]
      ghost := []
      pred := .assert .false_ (.ret ⟨"ret", .ret ()⟩) }
  folTerm := some (.symbol logicSizeSym)
  axioms := logicSizeAxioms

@[simp] theorem logicSize_arity : logicSize.arity = .one := rfl
@[simp] theorem logicSize_folSym : logicSize.folSym = some logicSizeSym := rfl

private theorem respects_updateConst {ρ : Env} (h : ρ.respects (some logicSizeSym))
    (x : String) (w : Runtime.Val) :
    (ρ.updateConst .value x w).respects (some logicSizeSym) := by
  simpa only [Env.respects, Env.updateConst_unary] using h

private theorem szTerm_eval {ρ : Env} (h : ρ.respects (some logicSizeSym)) (t : Term .value) :
    (szTerm t).eval ρ = .int (size (t.eval ρ)) := by
  simp only [szTerm, unTerm, Term.eval, UnOp.eval]
  rw [show ρ.unary .value .value "logic_size" = logicSizeSym.interp from h]
  rfl

private theorem logicSizeAxioms_wfIn :
    ∀ a ∈ logicSizeAxioms, a.formula.wfIn (Intrinsic.sigOf [logicSize]) := by
  intro a ha
  simp only [logicSizeAxioms, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> (apply Formula.checkWf_ok; rfl)

private theorem logicSizeAxioms_eval {ρ : Env} (h : ρ.respects (some logicSizeSym)) :
    ∀ a ∈ logicSizeAxioms, a.formula.eval ρ := by
  have hsz : ∀ (w : Runtime.Val) (t : Term .value),
      (szTerm t).eval (ρ.updateConst .value "v" w)
        = .int (size (t.eval (ρ.updateConst .value "v" w))) :=
    fun w t => szTerm_eval (respects_updateConst h "v" w) t
  intro a ha
  simp only [logicSizeAxioms, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sizeAxiom, Formula.eval] <;> intro w <;>
    simp only [szInt, hsz, sizeVar, sizeComponents, Term.eval, UnOp.eval, Const.denote,
      Env.lookupConst_updateConst_same, UnPred.eval, BinPred.eval, BinOp.eval]
  · exact size_nonneg w
  · rintro ⟨hinj, htup⟩; cases w <;> simp_all [size]
  · intro hinj; cases w <;> simp_all [size]
  · rintro ⟨htup, hnil⟩; cases w <;> simp_all [size, sizeTuple]
  · rintro ⟨htup, hcons⟩
    cases w with
    | tuple vs => cases vs <;> simp_all [size, sizeTuple]
    | _ => simp_all

/-- The intrinsic is sound. Both its specification and its weakest precondition
    are false, so only the axioms carry content. -/
@[reducible] def logicSizeSound : IntrinsicSound [logicSize] logicSize where
  argLen := rfl
  specWf := by
    intro Δ _ _
    simp [logicSize, Intrinsic.specArgs, PredTrans.wfIn, Assertion.wfIn]
    trivial
  bridge := by
    intro _ σ W vs ρ Φ _
    simp only [logicSize, PredTrans.apply, Assertion.pre]
    iintro H
    icases H with ⟨_, %hfalse, _⟩
    exact hfalse.elim
  wp_sound := by
    intro _ _ _ vs _
    match vs with
    | [] => exact false_elim
    | [_] => exact false_elim
    | _ :: _ :: _ => exact false_elim
  axiomWf := by
    intro Δ hsub hwf a ha
    exact Formula.wfIn_mono _ (logicSizeAxioms_wfIn a ha) hsub hwf
  proof := by
    intro ρ hdeps a ha
    exact logicSizeAxioms_eval (by simpa [logicSize] using hdeps logicSize (by simp)) a ha
  folWf := by
    rintro _ ⟨rfl⟩
    trivial

instance : IntrinsicSound [logicSize] logicSize := logicSizeSound

end Intrinsics
end Stdlib

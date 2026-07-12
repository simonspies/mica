-- SUMMARY: Integer-arithmetic intrinsics (`Int.min`, `Int.max`) and their soundness instances.
import Mica.Stdlib.Combinators

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## FOL symbols

`Int.min` / `Int.max` are uninterpreted binary FOL function symbols at the
value sort. Their standard interpretation is Lean's `min` / `max` on the
integer projection of the value (matching FOL's `toInt`, which sends
non-integer values to `0`), so the interpretation is *total*: it agrees with
the defining axiom for every value, not only the integer ones. -/

/-- FOL symbol for `Int.min`. -/
def intMinSym : FOL.Symbol .two where
  name   := "int_min"
  interp := fun (a, b) => .int (min (valInt a) (valInt b))

/-- FOL symbol for `Int.max`. -/
def intMaxSym : FOL.Symbol .two where
  name   := "int_max"
  interp := fun (a, b) => .int (max (valInt a) (valInt b))

@[simp] theorem intMinSym_name : intMinSym.name = "int_min" := rfl
@[simp] theorem intMaxSym_name : intMaxSym.name = "int_max" := rfl

/-! ## Defining axioms

`toInt (int_min x y) = ite (y ≥ x) x y` and the mirror for `max`, stated over
the integer projection so they constrain all values. -/

def intMinDefAxiom : Formula :=
  .all "x" .value <| .forall_ "y" .value
    [.term (binTerm "int_min" (.var .value "x") (.var .value "y"))] <|
    .eq .int
      (.unop .toInt (binTerm "int_min" (.var .value "x") (.var .value "y")))
      (.ite (.binop .ge (.unop .toInt (.var .value "y")) (.unop .toInt (.var .value "x")))
            (.unop .toInt (.var .value "x"))
            (.unop .toInt (.var .value "y")))

def intMaxDefAxiom : Formula :=
  .all "x" .value <| .forall_ "y" .value
    [.term (binTerm "int_max" (.var .value "x") (.var .value "y"))] <|
    .eq .int
      (.unop .toInt (binTerm "int_max" (.var .value "x") (.var .value "y")))
      (.ite (.binop .ge (.unop .toInt (.var .value "x")) (.unop .toInt (.var .value "y")))
            (.unop .toInt (.var .value "x"))
            (.unop .toInt (.var .value "y")))

/-! ## `Int.min` -/

/-- `Int.min`: arity-two integer intrinsic, built by `Pure.Binary`. Its spec ties
    the result to the `int_min` FOL symbol; the defining axiom pins that symbol
    down for the solver, while the standard interpretation pins it down for the
    soundness bridge. -/
def intMinB : Pure.Binary where
  name     := "int_min"
  path     := some ("Int", ["min"])
  arg₁     := .int
  arg₂     := .int
  res      := .int
  f        := (min : Int → Int → Int)
  dom      := fun _ _ => True
  pre      := none
  typing   := monoTyping .two
  defAxiom := intMinDefAxiom

def intMin : Intrinsic := intMinB.toIntrinsic

@[simp] theorem intMin_folSym : intMin.folSym = some intMinSym := rfl
@[simp] theorem intMin_arity : intMin.arity = .two := rfl

def intMinLawful : intMinB.Lawful where
  argL₁        := Embedding.lawfulInt
  argL₂        := Embedding.lawfulInt
  resL         := Embedding.lawfulInt
  domSound     := fun _ _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ _ => sep_emp.1
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by
    intrinsic_def_eval [binTerm, intMinB, intMinDefAxiom]
    intro x y
    rw [min_def, Bool.cond_decide]; congr 1

instance : IntrinsicSound [intMin] intMin := intMinLawful.sound

/-! ## `Int.max` -/

/-- `Int.max`: arity-two integer intrinsic, mirroring `Int.min`. -/
def intMaxB : Pure.Binary where
  name     := "int_max"
  path     := some ("Int", ["max"])
  arg₁     := .int
  arg₂     := .int
  res      := .int
  f        := (max : Int → Int → Int)
  dom      := fun _ _ => True
  pre      := none
  typing   := monoTyping .two
  defAxiom := intMaxDefAxiom

def intMax : Intrinsic := intMaxB.toIntrinsic

@[simp] theorem intMax_folSym : intMax.folSym = some intMaxSym := rfl
@[simp] theorem intMax_arity : intMax.arity = .two := rfl

def intMaxLawful : intMaxB.Lawful where
  argL₁        := Embedding.lawfulInt
  argL₂        := Embedding.lawfulInt
  resL         := Embedding.lawfulInt
  domSound     := fun _ _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ _ => sep_emp.1
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by
    intrinsic_def_eval [binTerm, intMaxB, intMaxDefAxiom]
    intro x y
    rw [max_comm, max_def, Bool.cond_decide]; congr 1

instance : IntrinsicSound [intMax] intMax := intMaxLawful.sound

end Intrinsics
end Stdlib

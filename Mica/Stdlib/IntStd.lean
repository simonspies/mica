-- SUMMARY: Integer-arithmetic intrinsics (`Int.min`, `Int.max`) and their soundness instances.
import Mica.Stdlib.Combinators

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## FOL symbols and their defining axioms

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

private def intMinTerm (x y : Term .value) : Term .value :=
  .binop (.uninterpreted intMinSym.name .value .value .value) x y

private def intMaxTerm (x y : Term .value) : Term .value :=
  .binop (.uninterpreted intMaxSym.name .value .value .value) x y

/-- Defining axiom for `Int.min`: `toInt (int_min x y) = ite (x ≤ y) x y`,
    stated over the integer projection so it constrains all values. -/
def intMinDefAxiom : Formula :=
  .all "x" .value <| .forall_ "y" .value
    [.term (intMinTerm (.var .value "x") (.var .value "y"))] <|
    .eq .int
      (.unop .toInt (intMinTerm (.var .value "x") (.var .value "y")))
      (.ite (.binop .ge (.unop .toInt (.var .value "y")) (.unop .toInt (.var .value "x")))
            (.unop .toInt (.var .value "x"))
            (.unop .toInt (.var .value "y")))

/-- Defining axiom for `Int.max`: `toInt (int_max x y) = ite (x ≥ y) x y`. -/
def intMaxDefAxiom : Formula :=
  .all "x" .value <| .forall_ "y" .value
    [.term (intMaxTerm (.var .value "x") (.var .value "y"))] <|
    .eq .int
      (.unop .toInt (intMaxTerm (.var .value "x") (.var .value "y")))
      (.ite (.binop .ge (.unop .toInt (.var .value "x")) (.unop .toInt (.var .value "y")))
            (.unop .toInt (.var .value "x"))
            (.unop .toInt (.var .value "y")))

/-! ## Per-operation axiom-evaluation helpers -/

private theorem min_axiom_eval (ρ : Env)
    (hρ : ρ.binary .value .value .value "int_min"
      = fun a b => intMinSym.interp (a, b)) (x y : Runtime.Val) :
    (UnOp.eval ρ .toInt (ρ.binary .value .value .value "int_min" x y))
      = (bif BinOp.eval ρ .ge (UnOp.eval ρ .toInt y) (UnOp.eval ρ .toInt x) then
          UnOp.eval ρ .toInt x else UnOp.eval ρ .toInt y) := by
  rw [hρ]
  simp only [UnOp.eval, BinOp.eval, Bool.cond_decide]
  change min (valInt x) (valInt y) = if valInt x ≤ valInt y then valInt x else valInt y
  by_cases h : valInt x ≤ valInt y
  · rw [if_pos h, min_eq_left h]
  · have hyx : valInt y ≤ valInt x := by omega
    rw [if_neg h, min_eq_right hyx]

private theorem max_axiom_eval (ρ : Env)
    (hρ : ρ.binary .value .value .value "int_max"
      = fun a b => intMaxSym.interp (a, b)) (x y : Runtime.Val) :
    (UnOp.eval ρ .toInt (ρ.binary .value .value .value "int_max" x y))
      = (bif BinOp.eval ρ .ge (UnOp.eval ρ .toInt x) (UnOp.eval ρ .toInt y) then
          UnOp.eval ρ .toInt x else UnOp.eval ρ .toInt y) := by
  rw [hρ]
  simp only [UnOp.eval, BinOp.eval, Bool.cond_decide]
  change max (valInt x) (valInt y) = if valInt y ≤ valInt x then valInt x else valInt y
  by_cases h : valInt y ≤ valInt x
  · rw [if_pos h, max_eq_left h]
  · have hxy : valInt x ≤ valInt y := by omega
    rw [if_neg h, max_eq_right hxy]

/-! ## `Int.min` -/

/-- `Int.min`: arity-two integer intrinsic, built by `Pure.Binary`. Its spec ties
    the result to the `int_min` FOL symbol; the defining axiom pins that symbol
    down for the solver, while the standard interpretation pins it down for the
    soundness bridge. -/
def intMinB : Pure.Binary where
  name     := "int_min"
  path     := some ("Int", ["min"])
  arg      := .int
  res      := .int
  f        := (min : Int → Int → Int)
  defAxiom := intMinDefAxiom

def intMin : Intrinsic := intMinB.toIntrinsic

@[simp] theorem intMin_folSym : intMin.folSym = some intMinSym := rfl
@[simp] theorem intMin_arity : intMin.arity = .two := rfl

def intMinLawful : intMinB.Lawful where
  argL       := Embedding.lawfulInt
  resL       := Embedding.lawfulInt
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by
    simp only [intMinB, Pure.Binary.toIntrinsic, Pure.Binary.sym]
    simp [intMinDefAxiom, intMinTerm, Intrinsic.sigOf, Intrinsic.foldSig,
      Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn, Signature.extendWithSym,
      Signature.empty, Signature.addBinary, Signature.declVar, Signature.addVar,
      Signature.remove]
  typeWf     := by
    simp only [intMinB, Pure.Binary.typeAxiom, Pure.Binary.opTerm, Pure.Binary.toIntrinsic,
      Pure.Binary.sym, Embedding.int]
    simp [Intrinsic.sigOf, Intrinsic.foldSig, Formula.wfIn, Term.wfIn, BinOp.wfIn,
      UnPred.wfIn, Signature.extendWithSym, Signature.empty, Signature.addBinary,
      Signature.declVar, Signature.addVar, Signature.remove]
  defEval    := by
    intro ρ hρ
    simp only [Env.respects] at hρ
    simp only [intMinB, intMinDefAxiom, Formula.all, Formula.eval]
    intro x y
    have hb : ((ρ.updateConst .value "x" x).updateConst .value "y" y).binary
        .value .value .value "int_min" = fun a b => intMinSym.interp (a, b) := by
      rw [Env.updateConst_binary, Env.updateConst_binary]
      simpa [intMinSym, intMinB, Pure.Binary.sym, Embedding.int] using hρ
    simpa [intMinTerm, Term.eval, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "x" ≠ "y" by decide)] using
      min_axiom_eval (((ρ.updateConst .value "x" x).updateConst .value "y" y)) hb x y

instance : IntrinsicSound [intMin] intMin := intMinLawful.sound

/-! ## `Int.max` -/

/-- `Int.max`: arity-two integer intrinsic, mirroring `Int.min`. -/
def intMaxB : Pure.Binary where
  name     := "int_max"
  path     := some ("Int", ["max"])
  arg      := .int
  res      := .int
  f        := (max : Int → Int → Int)
  defAxiom := intMaxDefAxiom

def intMax : Intrinsic := intMaxB.toIntrinsic

@[simp] theorem intMax_folSym : intMax.folSym = some intMaxSym := rfl
@[simp] theorem intMax_arity : intMax.arity = .two := rfl

def intMaxLawful : intMaxB.Lawful where
  argL       := Embedding.lawfulInt
  resL       := Embedding.lawfulInt
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by
    simp only [intMaxB, Pure.Binary.toIntrinsic, Pure.Binary.sym]
    simp [intMaxDefAxiom, intMaxTerm, Intrinsic.sigOf, Intrinsic.foldSig,
      Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn, Signature.extendWithSym,
      Signature.empty, Signature.addBinary, Signature.declVar, Signature.addVar,
      Signature.remove]
  typeWf     := by
    simp only [intMaxB, Pure.Binary.typeAxiom, Pure.Binary.opTerm, Pure.Binary.toIntrinsic,
      Pure.Binary.sym, Embedding.int]
    simp [Intrinsic.sigOf, Intrinsic.foldSig, Formula.wfIn, Term.wfIn, BinOp.wfIn,
      UnPred.wfIn, Signature.extendWithSym, Signature.empty, Signature.addBinary,
      Signature.declVar, Signature.addVar, Signature.remove]
  defEval    := by
    intro ρ hρ
    simp only [Env.respects] at hρ
    simp only [intMaxB, intMaxDefAxiom, Formula.all, Formula.eval]
    intro x y
    have hb : ((ρ.updateConst .value "x" x).updateConst .value "y" y).binary
        .value .value .value "int_max" = fun a b => intMaxSym.interp (a, b) := by
      rw [Env.updateConst_binary, Env.updateConst_binary]
      simpa [intMaxSym, intMaxB, Pure.Binary.sym, Embedding.int] using hρ
    simpa [intMaxTerm, Term.eval, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "x" ≠ "y" by decide)] using
      max_axiom_eval (((ρ.updateConst .value "x" x).updateConst .value "y" y)) hb x y

instance : IntrinsicSound [intMax] intMax := intMaxLawful.sound

end Intrinsics
end Stdlib

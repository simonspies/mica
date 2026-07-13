-- SUMMARY: IEEE binary64 float intrinsics (`Float.abs`, `add`, `min`, `equal`, `nan`, …) and soundness instances.
import Mica.Stdlib.Combinators
import Mica.Stdlib.IntStd

open Iris Iris.BI

/-! ## Derived `FloatBits` operations

`is_finite`, `min`, and `max` are defined here from the `FloatBits` primitives
(decode/compute/encode ops in `Mica/FOL/Terms.lean`), with exactly the `bif`-structure
used by their definitional axioms below, so those axioms hold by `rfl` and add no assumptions
beyond the primitives. They are kept out of the FOL layer because no term-level
`UnOp`/`BinOp` head reduces to them; only the intrinsics here use them. -/
namespace FloatBits

/-- OCaml `Float.is_finite`: not infinite and not NaN. -/
def isFinite (a : UInt64) : Bool :=
  bif isInf a then false else bif isNaN a then false else true

/-- OCaml `Float.min`: NaN if either operand is NaN; otherwise the lesser, with
the `min (-0.) (+0.) = -0.` tie broken by the sign bit (`isNegative`). -/
def min (a b : UInt64) : UInt64 :=
  bif isNaN a then nan
  else bif isNaN b then nan
  else bif lt a b then a
  else bif lt b a then b
  else bif isNegative a then a else b

/-- OCaml `Float.max`: NaN if either operand is NaN; otherwise the greater, with
the `max (-0.) (+0.) = +0.` tie broken by the sign bit (`isNegative`). -/
def max (a b : UInt64) : UInt64 :=
  bif isNaN a then nan
  else bif isNaN b then nan
  else bif lt a b then b
  else bif lt b a then a
  else bif isNegative a then b else a

end FloatBits

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## FOL symbols -/

def floatAbsSym : FOL.Symbol .one where
  name := "float_abs"; interp := fun a => .float (FloatBits.abs (valFloat a))
def floatNegSym : FOL.Symbol .one where
  name := "float_neg"; interp := fun a => .float (FloatBits.neg (valFloat a))
def floatSqrtSym : FOL.Symbol .one where
  name := "float_sqrt"; interp := fun a => .float (FloatBits.sqrt (valFloat a))
def floatIsNanSym : FOL.Symbol .one where
  name := "float_is_nan"; interp := fun a => .bool (FloatBits.isNaN (valFloat a))
def floatIsFiniteSym : FOL.Symbol .one where
  name := "float_is_finite"; interp := fun a => .bool (FloatBits.isFinite (valFloat a))
def floatOfIntSym : FOL.Symbol .one where
  name := "float_of_int"; interp := fun a => .float (FloatBits.ofInt (valInt a))
def floatAddSym : FOL.Symbol .two where
  name := "float_add"; interp := fun (a, b) => .float (FloatBits.add (valFloat a) (valFloat b))
def floatSubSym : FOL.Symbol .two where
  name := "float_sub"; interp := fun (a, b) => .float (FloatBits.sub (valFloat a) (valFloat b))
def floatMulSym : FOL.Symbol .two where
  name := "float_mul"; interp := fun (a, b) => .float (FloatBits.mul (valFloat a) (valFloat b))
def floatDivSym : FOL.Symbol .two where
  name := "float_div"; interp := fun (a, b) => .float (FloatBits.div (valFloat a) (valFloat b))
def floatMinSym : FOL.Symbol .two where
  name := "float_min"; interp := fun (a, b) => .float (FloatBits.min (valFloat a) (valFloat b))
def floatMaxSym : FOL.Symbol .two where
  name := "float_max"; interp := fun (a, b) => .float (FloatBits.max (valFloat a) (valFloat b))
def floatEqualSym : FOL.Symbol .two where
  name := "float_equal"; interp := fun (a, b) => .bool (FloatBits.eq (valFloat a) (valFloat b))
def floatLtSym : FOL.Symbol .two where
  name := "float_lt"; interp := fun (a, b) => .bool (FloatBits.lt (valFloat a) (valFloat b))
def floatLeSym : FOL.Symbol .two where
  name := "float_le"; interp := fun (a, b) => .bool (FloatBits.le (valFloat a) (valFloat b))
def floatNanSym : FOL.Symbol .zero where
  name := "float_nan"; interp := fun () => .float FloatBits.nan
def floatInfinitySym : FOL.Symbol .zero where
  name := "float_infinity"; interp := fun () => .float FloatBits.posInf
def floatNegInfinitySym : FOL.Symbol .zero where
  name := "float_neg_infinity"; interp := fun () => .float FloatBits.negInf

@[simp] theorem floatAbsSym_name : floatAbsSym.name = "float_abs" := rfl
@[simp] theorem floatNegSym_name : floatNegSym.name = "float_neg" := rfl
@[simp] theorem floatSqrtSym_name : floatSqrtSym.name = "float_sqrt" := rfl
@[simp] theorem floatIsNanSym_name : floatIsNanSym.name = "float_is_nan" := rfl
@[simp] theorem floatIsFiniteSym_name : floatIsFiniteSym.name = "float_is_finite" := rfl
@[simp] theorem floatOfIntSym_name : floatOfIntSym.name = "float_of_int" := rfl
@[simp] theorem floatAddSym_name : floatAddSym.name = "float_add" := rfl
@[simp] theorem floatSubSym_name : floatSubSym.name = "float_sub" := rfl
@[simp] theorem floatMulSym_name : floatMulSym.name = "float_mul" := rfl
@[simp] theorem floatDivSym_name : floatDivSym.name = "float_div" := rfl
@[simp] theorem floatMinSym_name : floatMinSym.name = "float_min" := rfl
@[simp] theorem floatMaxSym_name : floatMaxSym.name = "float_max" := rfl
@[simp] theorem floatEqualSym_name : floatEqualSym.name = "float_equal" := rfl
@[simp] theorem floatLtSym_name : floatLtSym.name = "float_lt" := rfl
@[simp] theorem floatLeSym_name : floatLeSym.name = "float_le" := rfl
@[simp] theorem floatNanSym_name : floatNanSym.name = "float_nan" := rfl
@[simp] theorem floatInfinitySym_name : floatInfinitySym.name = "float_infinity" := rfl
@[simp] theorem floatNegInfinitySym_name :
    floatNegInfinitySym.name = "float_neg_infinity" := rfl

/-! ## Unary float intrinsics -/

def floatAbsDefAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_abs" (.var .value "a"))] <|
    .eq .float (.unop .toFloat (unTerm "float_abs" (.var .value "a")))
      (.unop .fpAbs (.unop .toFloat (.var .value "a")))

def floatAbsB : Pure.Unary where
  name     := "float_abs"
  path     := some ("Float", ["abs"])
  arg      := .float
  res      := .float
  f        := FloatBits.abs
  typing   := monoTyping .one
  defAxiom := floatAbsDefAxiom

def floatAbs : Intrinsic := floatAbsB.toIntrinsic

@[simp] theorem floatAbs_folSym : floatAbs.folSym = some floatAbsSym := rfl
@[simp] theorem floatAbs_arity : floatAbs.arity = .one := rfl

def floatAbsLawful : floatAbsB.Lawful where
  argL       := Embedding.lawfulFloat
  resL       := Embedding.lawfulFloat
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [unTerm, floatAbsB, floatAbsDefAxiom]; intros; rfl

instance : IntrinsicSound [floatAbs] floatAbs := floatAbsLawful.sound

def floatNegDefAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_neg" (.var .value "a"))] <|
    .eq .float (.unop .toFloat (unTerm "float_neg" (.var .value "a")))
      (.unop .fpNeg (.unop .toFloat (.var .value "a")))

def floatNegB : Pure.Unary where
  name     := "float_neg"
  path     := some ("Float", ["neg"])
  arg      := .float
  res      := .float
  f        := FloatBits.neg
  typing   := monoTyping .one
  defAxiom := floatNegDefAxiom

def floatNeg : Intrinsic := floatNegB.toIntrinsic

@[simp] theorem floatNeg_folSym : floatNeg.folSym = some floatNegSym := rfl
@[simp] theorem floatNeg_arity : floatNeg.arity = .one := rfl

def floatNegLawful : floatNegB.Lawful where
  argL       := Embedding.lawfulFloat
  resL       := Embedding.lawfulFloat
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [unTerm, floatNegB, floatNegDefAxiom]; intros; rfl

instance : IntrinsicSound [floatNeg] floatNeg := floatNegLawful.sound

def floatSqrtDefAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_sqrt" (.var .value "a"))] <|
    .eq .float (.unop .toFloat (unTerm "float_sqrt" (.var .value "a")))
      (.unop .fpSqrt (.unop .toFloat (.var .value "a")))

def floatSqrtB : Pure.Unary where
  name     := "float_sqrt"
  path     := some ("Float", ["sqrt"])
  arg      := .float
  res      := .float
  f        := FloatBits.sqrt
  typing   := monoTyping .one
  defAxiom := floatSqrtDefAxiom

def floatSqrt : Intrinsic := floatSqrtB.toIntrinsic

@[simp] theorem floatSqrt_folSym : floatSqrt.folSym = some floatSqrtSym := rfl
@[simp] theorem floatSqrt_arity : floatSqrt.arity = .one := rfl

def floatSqrtLawful : floatSqrtB.Lawful where
  argL       := Embedding.lawfulFloat
  resL       := Embedding.lawfulFloat
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [unTerm, floatSqrtB, floatSqrtDefAxiom]; intros; rfl

instance : IntrinsicSound [floatSqrt] floatSqrt := floatSqrtLawful.sound

def floatIsNanDefAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_is_nan" (.var .value "a"))] <|
    .eq .bool (.unop .toBool (unTerm "float_is_nan" (.var .value "a")))
      (.unop .fpIsNaN (.unop .toFloat (.var .value "a")))

def floatIsNanB : Pure.Unary where
  name     := "float_is_nan"
  path     := some ("Float", ["is_nan"])
  arg      := .float
  res      := .bool
  f        := FloatBits.isNaN
  typing   := monoTyping .one
  defAxiom := floatIsNanDefAxiom

def floatIsNan : Intrinsic := floatIsNanB.toIntrinsic

@[simp] theorem floatIsNan_folSym : floatIsNan.folSym = some floatIsNanSym := rfl
@[simp] theorem floatIsNan_arity : floatIsNan.arity = .one := rfl

def floatIsNanLawful : floatIsNanB.Lawful where
  argL       := Embedding.lawfulFloat
  resL       := Embedding.lawfulBool
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [unTerm, floatIsNanB, floatIsNanDefAxiom]; intros; rfl

instance : IntrinsicSound [floatIsNan] floatIsNan := floatIsNanLawful.sound

/-- `is_finite a` decodes to `¬infinite ∧ ¬nan`, expressed via the Z3 primitives
`fp.isInfinite`/`fp.isNaN`. Mirrors `FloatBits.isFinite`. -/
def floatIsFiniteDefAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_is_finite" (.var .value "a"))] <|
    .eq .bool (.unop .toBool (unTerm "float_is_finite" (.var .value "a")))
      (.ite (.unop .fpIsInfinite (.unop .toFloat (.var .value "a"))) (.const (.b false))
        (.ite (.unop .fpIsNaN (.unop .toFloat (.var .value "a"))) (.const (.b false))
          (.const (.b true))))

def floatIsFiniteB : Pure.Unary where
  name     := "float_is_finite"
  path     := some ("Float", ["is_finite"])
  arg      := .float
  res      := .bool
  f        := FloatBits.isFinite
  typing   := monoTyping .one
  defAxiom := floatIsFiniteDefAxiom

def floatIsFinite : Intrinsic := floatIsFiniteB.toIntrinsic

@[simp] theorem floatIsFinite_folSym : floatIsFinite.folSym = some floatIsFiniteSym := rfl
@[simp] theorem floatIsFinite_arity : floatIsFinite.arity = .one := rfl

def floatIsFiniteLawful : floatIsFiniteB.Lawful where
  argL       := Embedding.lawfulFloat
  resL       := Embedding.lawfulBool
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [unTerm, floatIsFiniteB, floatIsFiniteDefAxiom, FloatBits.isFinite]; intros; rfl

instance : IntrinsicSound [floatIsFinite] floatIsFinite := floatIsFiniteLawful.sound

def floatOfIntDefAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_of_int" (.var .value "a"))] <|
    .eq .float (.unop .toFloat (unTerm "float_of_int" (.var .value "a")))
      (.unop .fpOfInt (.unop .toInt (.var .value "a")))

def floatOfIntB : Pure.Unary where
  name     := "float_of_int"
  path     := some ("Float", ["of_int"])
  arg      := .int
  res      := .float
  f        := FloatBits.ofInt
  typing   := monoTyping .one
  defAxiom := floatOfIntDefAxiom

def floatOfInt : Intrinsic := floatOfIntB.toIntrinsic

@[simp] theorem floatOfInt_folSym : floatOfInt.folSym = some floatOfIntSym := rfl
@[simp] theorem floatOfInt_arity : floatOfInt.arity = .one := rfl

def floatOfIntLawful : floatOfIntB.Lawful where
  argL       := Embedding.lawfulInt
  resL       := Embedding.lawfulFloat
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [unTerm, floatOfIntB, floatOfIntDefAxiom]; intros; rfl

instance : IntrinsicSound [floatOfInt] floatOfInt := floatOfIntLawful.sound

private def binFloatDefAxiom (sym : FOL.Symbol .two) (op : BinOp .float .float .float) : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm sym.name (.var .value "a") (.var .value "b"))] <|
    .eq .float (.unop .toFloat (binTerm sym.name (.var .value "a") (.var .value "b")))
      (.binop op (.unop .toFloat (.var .value "a")) (.unop .toFloat (.var .value "b")))

def floatAddB : Pure.Binary where
  name     := "float_add"
  path     := some ("Float", ["add"])
  arg₁     := .float
  arg₂     := .float
  res      := .float
  f        := FloatBits.add
  typing   := monoTyping .two
  defAxiom := binFloatDefAxiom floatAddSym .fpAdd

def floatAdd : Intrinsic := floatAddB.toIntrinsic

@[simp] theorem floatAdd_folSym : floatAdd.folSym = some floatAddSym := rfl
@[simp] theorem floatAdd_arity : floatAdd.arity = .two := rfl

def floatAddLawful : floatAddB.Lawful where
  argL₁      := Embedding.lawfulFloat
  argL₂      := Embedding.lawfulFloat
  resL       := Embedding.lawfulFloat
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [binTerm, floatAddB, floatAddSym, binFloatDefAxiom]; intros; rfl

instance : IntrinsicSound [floatAdd] floatAdd := floatAddLawful.sound

def floatSubB : Pure.Binary where
  name     := "float_sub"
  path     := some ("Float", ["sub"])
  arg₁     := .float
  arg₂     := .float
  res      := .float
  f        := FloatBits.sub
  typing   := monoTyping .two
  defAxiom := binFloatDefAxiom floatSubSym .fpSub

def floatSub : Intrinsic := floatSubB.toIntrinsic

@[simp] theorem floatSub_folSym : floatSub.folSym = some floatSubSym := rfl
@[simp] theorem floatSub_arity : floatSub.arity = .two := rfl

def floatSubLawful : floatSubB.Lawful where
  argL₁      := Embedding.lawfulFloat
  argL₂      := Embedding.lawfulFloat
  resL       := Embedding.lawfulFloat
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [binTerm, floatSubB, floatSubSym, binFloatDefAxiom]; intros; rfl

instance : IntrinsicSound [floatSub] floatSub := floatSubLawful.sound

def floatMulB : Pure.Binary where
  name     := "float_mul"
  path     := some ("Float", ["mul"])
  arg₁     := .float
  arg₂     := .float
  res      := .float
  f        := FloatBits.mul
  typing   := monoTyping .two
  defAxiom := binFloatDefAxiom floatMulSym .fpMul

def floatMul : Intrinsic := floatMulB.toIntrinsic

@[simp] theorem floatMul_folSym : floatMul.folSym = some floatMulSym := rfl
@[simp] theorem floatMul_arity : floatMul.arity = .two := rfl

def floatMulLawful : floatMulB.Lawful where
  argL₁      := Embedding.lawfulFloat
  argL₂      := Embedding.lawfulFloat
  resL       := Embedding.lawfulFloat
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [binTerm, floatMulB, floatMulSym, binFloatDefAxiom]; intros; rfl

instance : IntrinsicSound [floatMul] floatMul := floatMulLawful.sound

def floatDivB : Pure.Binary where
  name     := "float_div"
  path     := some ("Float", ["div"])
  arg₁     := .float
  arg₂     := .float
  res      := .float
  f        := FloatBits.div
  typing   := monoTyping .two
  defAxiom := binFloatDefAxiom floatDivSym .fpDiv

def floatDiv : Intrinsic := floatDivB.toIntrinsic

@[simp] theorem floatDiv_folSym : floatDiv.folSym = some floatDivSym := rfl
@[simp] theorem floatDiv_arity : floatDiv.arity = .two := rfl

def floatDivLawful : floatDivB.Lawful where
  argL₁      := Embedding.lawfulFloat
  argL₂      := Embedding.lawfulFloat
  resL       := Embedding.lawfulFloat
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [binTerm, floatDivB, floatDivSym, binFloatDefAxiom]; intros; rfl

instance : IntrinsicSound [floatDiv] floatDiv := floatDivLawful.sound

/-- `Float.min`, OCaml-faithful incl. signed zero. -/
def floatMinDefAxiom : Formula :=
  let ta : Term .float := .unop .toFloat (.var .value "a")
  let tb : Term .float := .unop .toFloat (.var .value "b")
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm "float_min" (.var .value "a") (.var .value "b"))] <|
    .eq .float (.unop .toFloat (binTerm "float_min" (.var .value "a") (.var .value "b")))
      (.ite (.unop .fpIsNaN ta) (.const .fpNaN)
        (.ite (.unop .fpIsNaN tb) (.const .fpNaN)
          (.ite (.binop .fpLt ta tb) ta
            (.ite (.binop .fpLt tb ta) tb
              (.ite (.unop .fpIsNegative ta) ta tb)))))

def floatMinB : Pure.Binary where
  name     := "float_min"
  path     := some ("Float", ["min"])
  arg₁     := .float
  arg₂     := .float
  res      := .float
  f        := FloatBits.min
  typing   := monoTyping .two
  defAxiom := floatMinDefAxiom

def floatMin : Intrinsic := floatMinB.toIntrinsic

@[simp] theorem floatMin_folSym : floatMin.folSym = some floatMinSym := rfl
@[simp] theorem floatMin_arity : floatMin.arity = .two := rfl

def floatMinLawful : floatMinB.Lawful where
  argL₁      := Embedding.lawfulFloat
  argL₂      := Embedding.lawfulFloat
  resL       := Embedding.lawfulFloat
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [binTerm, floatMinB, floatMinDefAxiom, FloatBits.min]; intros; rfl

instance : IntrinsicSound [floatMin] floatMin := floatMinLawful.sound

/-- `Float.max`, OCaml-faithful incl. signed zero. -/
def floatMaxDefAxiom : Formula :=
  let ta : Term .float := .unop .toFloat (.var .value "a")
  let tb : Term .float := .unop .toFloat (.var .value "b")
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm "float_max" (.var .value "a") (.var .value "b"))] <|
    .eq .float (.unop .toFloat (binTerm "float_max" (.var .value "a") (.var .value "b")))
      (.ite (.unop .fpIsNaN ta) (.const .fpNaN)
        (.ite (.unop .fpIsNaN tb) (.const .fpNaN)
          (.ite (.binop .fpLt ta tb) tb
            (.ite (.binop .fpLt tb ta) ta
              (.ite (.unop .fpIsNegative ta) tb ta)))))

def floatMaxB : Pure.Binary where
  name     := "float_max"
  path     := some ("Float", ["max"])
  arg₁     := .float
  arg₂     := .float
  res      := .float
  f        := FloatBits.max
  typing   := monoTyping .two
  defAxiom := floatMaxDefAxiom

def floatMax : Intrinsic := floatMaxB.toIntrinsic

@[simp] theorem floatMax_folSym : floatMax.folSym = some floatMaxSym := rfl
@[simp] theorem floatMax_arity : floatMax.arity = .two := rfl

def floatMaxLawful : floatMaxB.Lawful where
  argL₁      := Embedding.lawfulFloat
  argL₂      := Embedding.lawfulFloat
  resL       := Embedding.lawfulFloat
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [binTerm, floatMaxB, floatMaxDefAxiom, FloatBits.max]; intros; rfl

instance : IntrinsicSound [floatMax] floatMax := floatMaxLawful.sound

private def binFloatBoolDefAxiom (sym : FOL.Symbol .two) (op : BinOp .float .float .bool) : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm sym.name (.var .value "a") (.var .value "b"))] <|
    .eq .bool (.unop .toBool (binTerm sym.name (.var .value "a") (.var .value "b")))
      (.binop op (.unop .toFloat (.var .value "a")) (.unop .toFloat (.var .value "b")))

def floatEqualB : Pure.Binary where
  name     := "float_equal"
  path     := some ("Float", ["equal"])
  arg₁     := .float
  arg₂     := .float
  res      := .bool
  f        := FloatBits.eq
  typing   := monoTyping .two
  defAxiom := binFloatBoolDefAxiom floatEqualSym .fpEq

def floatEqual : Intrinsic := floatEqualB.toIntrinsic

@[simp] theorem floatEqual_folSym : floatEqual.folSym = some floatEqualSym := rfl
@[simp] theorem floatEqual_arity : floatEqual.arity = .two := rfl

def floatEqualLawful : floatEqualB.Lawful where
  argL₁      := Embedding.lawfulFloat
  argL₂      := Embedding.lawfulFloat
  resL       := Embedding.lawfulBool
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [binTerm, floatEqualB, floatEqualSym, binFloatBoolDefAxiom]; intros; rfl

instance : IntrinsicSound [floatEqual] floatEqual := floatEqualLawful.sound

def floatLtB : Pure.Binary where
  name     := "float_lt"
  path     := some ("Float", ["lt"])
  arg₁     := .float
  arg₂     := .float
  res      := .bool
  f        := FloatBits.lt
  typing   := monoTyping .two
  defAxiom := binFloatBoolDefAxiom floatLtSym .fpLt

def floatLt : Intrinsic := floatLtB.toIntrinsic

@[simp] theorem floatLt_folSym : floatLt.folSym = some floatLtSym := rfl
@[simp] theorem floatLt_arity : floatLt.arity = .two := rfl

def floatLtLawful : floatLtB.Lawful where
  argL₁      := Embedding.lawfulFloat
  argL₂      := Embedding.lawfulFloat
  resL       := Embedding.lawfulBool
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [binTerm, floatLtB, floatLtSym, binFloatBoolDefAxiom]; intros; rfl

instance : IntrinsicSound [floatLt] floatLt := floatLtLawful.sound

def floatLeB : Pure.Binary where
  name     := "float_le"
  path     := some ("Float", ["le"])
  arg₁     := .float
  arg₂     := .float
  res      := .bool
  f        := FloatBits.le
  typing   := monoTyping .two
  defAxiom := binFloatBoolDefAxiom floatLeSym .fpLe

def floatLe : Intrinsic := floatLeB.toIntrinsic

@[simp] theorem floatLe_folSym : floatLe.folSym = some floatLeSym := rfl
@[simp] theorem floatLe_arity : floatLe.arity = .two := rfl

def floatLeLawful : floatLeB.Lawful where
  argL₁      := Embedding.lawfulFloat
  argL₂      := Embedding.lawfulFloat
  resL       := Embedding.lawfulBool
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [binTerm, floatLeB, floatLeSym, binFloatBoolDefAxiom]; intros; rfl

instance : IntrinsicSound [floatLe] floatLe := floatLeLawful.sound

/-! ## Arity-zero float constants -/

private def zeroFloatDefAxiom (sym : FOL.Symbol .zero) (c : Const .float) : Formula :=
  .eq .float (.unop .toFloat (constTerm sym.name)) (.const c)

def floatNanB : Pure.Zero where
  name     := "float_nan"
  path     := some ("Float", ["nan"])
  res      := .float
  f        := FloatBits.nan
  typing   := monoTyping .zero
  defAxiom := zeroFloatDefAxiom floatNanSym .fpNaN

def floatNan : Intrinsic := floatNanB.toIntrinsic

@[simp] theorem floatNan_folSym : floatNan.folSym = some floatNanSym := rfl
@[simp] theorem floatNan_arity : floatNan.arity = .zero := rfl

def floatNanLawful : floatNanB.Lawful where
  resL       := Embedding.lawfulFloat
  nameFresh  := by decide
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [constTerm, floatNanB, floatNanSym, zeroFloatDefAxiom]

instance : IntrinsicSound [floatNan] floatNan := floatNanLawful.sound

def floatInfinityB : Pure.Zero where
  name     := "float_infinity"
  path     := some ("Float", ["infinity"])
  res      := .float
  f        := FloatBits.posInf
  typing   := monoTyping .zero
  defAxiom := zeroFloatDefAxiom floatInfinitySym .fpPosInf

def floatInfinity : Intrinsic := floatInfinityB.toIntrinsic

@[simp] theorem floatInfinity_folSym : floatInfinity.folSym = some floatInfinitySym := rfl
@[simp] theorem floatInfinity_arity : floatInfinity.arity = .zero := rfl

def floatInfinityLawful : floatInfinityB.Lawful where
  resL       := Embedding.lawfulFloat
  nameFresh  := by decide
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [constTerm, floatInfinityB, floatInfinitySym, zeroFloatDefAxiom]

instance : IntrinsicSound [floatInfinity] floatInfinity := floatInfinityLawful.sound

def floatNegInfinityB : Pure.Zero where
  name     := "float_neg_infinity"
  path     := some ("Float", ["neg_infinity"])
  res      := .float
  f        := FloatBits.negInf
  typing   := monoTyping .zero
  defAxiom := zeroFloatDefAxiom floatNegInfinitySym .fpNegInf

def floatNegInfinity : Intrinsic := floatNegInfinityB.toIntrinsic

@[simp] theorem floatNegInfinity_folSym :
    floatNegInfinity.folSym = some floatNegInfinitySym := rfl
@[simp] theorem floatNegInfinity_arity : floatNegInfinity.arity = .zero := rfl

def floatNegInfinityLawful : floatNegInfinityB.Lawful where
  resL       := Embedding.lawfulFloat
  nameFresh  := by decide
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [constTerm, floatNegInfinityB, floatNegInfinitySym, zeroFloatDefAxiom]

instance : IntrinsicSound [floatNegInfinity] floatNegInfinity := floatNegInfinityLawful.sound

end Intrinsics
end Stdlib

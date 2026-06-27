-- SUMMARY: Byte-string intrinsics (`String.length`, `cat`, `equal`, `starts_with`, `ends_with`) and soundness instances.
import Mica.Stdlib.IntStd

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## FOL symbols -/

/-- FOL symbol for `String.length`. -/
def stringLengthSym : FOL.Symbol .one where
  name   := "string_length"
  interp := fun a => .int (valStr a).length

/-- FOL symbol for `String.cat`. -/
def stringCatSym : FOL.Symbol .two where
  name   := "string_cat"
  interp := fun (a, b) => .str (valStr a ++ valStr b)

/-- FOL symbol for `String.equal`. -/
def stringEqualSym : FOL.Symbol .two where
  name   := "string_equal"
  interp := fun (a, b) => .bool (valStr a == valStr b)

/-- FOL symbol for `String.starts_with`. -/
def stringStartsWithSym : FOL.Symbol .two where
  name   := "string_starts_with"
  interp := fun (p, s) => .bool ((valStr p).isPrefixOf (valStr s))

/-- FOL symbol for `String.ends_with`. -/
def stringEndsWithSym : FOL.Symbol .two where
  name   := "string_ends_with"
  interp := fun (q, s) => .bool ((valStr q).isSuffixOf (valStr s))

@[simp] theorem stringLengthSym_name : stringLengthSym.name = "string_length" := rfl
@[simp] theorem stringCatSym_name : stringCatSym.name = "string_cat" := rfl
@[simp] theorem stringEqualSym_name : stringEqualSym.name = "string_equal" := rfl
@[simp] theorem stringStartsWithSym_name : stringStartsWithSym.name = "string_starts_with" := rfl
@[simp] theorem stringEndsWithSym_name : stringEndsWithSym.name = "string_ends_with" := rfl

/-! ## Defining axioms

Each intrinsic carries two axioms, both quantified over the **value sort**:
a *defining* axiom tying the symbol to Z3's native sequence theory (through the
`toString`/`toInt` projections), and a *typing* axiom asserting the result is
the expected value constructor (`is-of_int`/`is-of_string`/`is-of_bool`).

The typing axiom is what lets a bare value-level equality such as
`String.length s = 2` discharge: without it Z3 only knows the symbol's `toInt`
projection, not that the result *is* an integer value. Only the defining axiom
is written by hand here; the typing axiom is generated uniformly from the result
embedding by `Pure.Binary`/`Pure.Unary`. -/

def stringLengthDefAxiom : Formula :=
  .forall_ "s" .value [.term (unTerm "string_length" (.var .value "s"))] <|
    .eq .int
      (.unop .toInt (unTerm "string_length" (.var .value "s")))
      (.unop .seqLen (.unop .toString (.var .value "s")))

def stringCatDefAxiom : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm "string_cat" (.var .value "a") (.var .value "b"))] <|
    .eq .string
      (.unop .toString (binTerm "string_cat" (.var .value "a") (.var .value "b")))
      (.binop .seqConcat (.unop .toString (.var .value "a")) (.unop .toString (.var .value "b")))

def stringEqualDefAxiom : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm "string_equal" (.var .value "a") (.var .value "b"))] <|
    .eq .bool
      (.unop .toBool (binTerm "string_equal" (.var .value "a") (.var .value "b")))
      (.binop (.eq (τ := .string)) (.unop .toString (.var .value "a")) (.unop .toString (.var .value "b")))

def stringStartsWithDefAxiom : Formula :=
  .all "prefix" .value <| .forall_ "s" .value
    [.term (binTerm "string_starts_with" (.var .value "prefix") (.var .value "s"))] <|
    .eq .bool
      (.unop .toBool (binTerm "string_starts_with" (.var .value "prefix") (.var .value "s")))
      (.binop .seqPrefixOf (.unop .toString (.var .value "prefix")) (.unop .toString (.var .value "s")))

def stringEndsWithDefAxiom : Formula :=
  .all "suffix" .value <| .forall_ "s" .value
    [.term (binTerm "string_ends_with" (.var .value "suffix") (.var .value "s"))] <|
    .eq .bool
      (.unop .toBool (binTerm "string_ends_with" (.var .value "suffix") (.var .value "s")))
      (.binop .seqSuffixOf (.unop .toString (.var .value "suffix")) (.unop .toString (.var .value "s")))

/-! ## `String.length` -/

/-- `String.length`: byte length, built by `Pure.Unary`. -/
def stringLengthB : Pure.Unary where
  name     := "string_length"
  path     := some ("String", ["length"])
  arg      := .str
  res      := .int
  f        := (fun s => (s.length : Int) : List UInt8 → Int)
  defAxiom := stringLengthDefAxiom

def stringLength : Intrinsic := stringLengthB.toIntrinsic

@[simp] theorem stringLength_arity : stringLength.arity = .one := rfl
@[simp] theorem stringLength_folSym : stringLength.folSym = some stringLengthSym := rfl

def stringLengthLawful : stringLengthB.Lawful where
  argL       := Embedding.lawfulStr
  resL       := Embedding.lawfulInt
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [unTerm, stringLengthB, stringLengthDefAxiom]; intros; rfl

instance : IntrinsicSound [stringLength] stringLength := stringLengthLawful.sound

/-! ## `String.cat` -/

/-- `String.cat`: byte-string concatenation, built by `Pure.Binary`. -/
def stringCatB : Pure.Binary where
  name     := "string_cat"
  path     := some ("String", ["cat"])
  arg      := .str
  res      := .str
  f        := (fun x y => x ++ y : List UInt8 → List UInt8 → List UInt8)
  defAxiom := stringCatDefAxiom

def stringCat : Intrinsic := stringCatB.toIntrinsic

@[simp] theorem stringCat_arity : stringCat.arity = .two := rfl
@[simp] theorem stringCat_folSym : stringCat.folSym = some stringCatSym := rfl

def stringCatLawful : stringCatB.Lawful where
  argL       := Embedding.lawfulStr
  resL       := Embedding.lawfulStr
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by intrinsic_def_eval [binTerm, stringCatB, stringCatDefAxiom]; intros; rfl

instance : IntrinsicSound [stringCat] stringCat := stringCatLawful.sound

/-! ## `String.equal` -/

/-- `String.equal`: byte-string equality, built by `Pure.Binary`. -/
def stringEqualB : Pure.Binary where
  name     := "string_equal"
  path     := some ("String", ["equal"])
  arg      := .str
  res      := .bool
  f        := (fun x y => x == y : List UInt8 → List UInt8 → Bool)
  defAxiom := stringEqualDefAxiom

def stringEqual : Intrinsic := stringEqualB.toIntrinsic

@[simp] theorem stringEqual_arity : stringEqual.arity = .two := rfl
@[simp] theorem stringEqual_folSym : stringEqual.folSym = some stringEqualSym := rfl

def stringEqualLawful : stringEqualB.Lawful where
  argL       := Embedding.lawfulStr
  resL       := Embedding.lawfulBool
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by
    intrinsic_def_eval [binTerm, stringEqualB, stringEqualDefAxiom, Bool.beq_eq_decide_eq]
    intros; rfl

instance : IntrinsicSound [stringEqual] stringEqual := stringEqualLawful.sound

/-! ## `String.starts_with` -/

/-- `String.starts_with`: byte-string prefix test, built by `Pure.Binary`. -/
def stringStartsWithB : Pure.Binary where
  name     := "string_starts_with"
  path     := some ("String", ["starts_with"])
  arg      := .str
  res      := .bool
  f        := (fun x y => x.isPrefixOf y : List UInt8 → List UInt8 → Bool)
  defAxiom := stringStartsWithDefAxiom

def stringStartsWith : Intrinsic := stringStartsWithB.toIntrinsic

@[simp] theorem stringStartsWith_arity : stringStartsWith.arity = .two := rfl
@[simp] theorem stringStartsWith_folSym :
    stringStartsWith.folSym = some stringStartsWithSym := rfl

def stringStartsWithLawful : stringStartsWithB.Lawful where
  argL       := Embedding.lawfulStr
  resL       := Embedding.lawfulBool
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by
    intrinsic_def_eval [binTerm, stringStartsWithB, stringStartsWithDefAxiom]; intros; rfl

instance : IntrinsicSound [stringStartsWith] stringStartsWith := stringStartsWithLawful.sound

/-! ## `String.ends_with` -/

/-- `String.ends_with`: byte-string suffix test, built by `Pure.Binary`. -/
def stringEndsWithB : Pure.Binary where
  name     := "string_ends_with"
  path     := some ("String", ["ends_with"])
  arg      := .str
  res      := .bool
  f        := (fun x y => x.isSuffixOf y : List UInt8 → List UInt8 → Bool)
  defAxiom := stringEndsWithDefAxiom

def stringEndsWith : Intrinsic := stringEndsWithB.toIntrinsic

@[simp] theorem stringEndsWith_arity : stringEndsWith.arity = .two := rfl
@[simp] theorem stringEndsWith_folSym : stringEndsWith.folSym = some stringEndsWithSym := rfl

def stringEndsWithLawful : stringEndsWithB.Lawful where
  argL       := Embedding.lawfulStr
  resL       := Embedding.lawfulBool
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf      := by apply Formula.checkWf_ok; rfl
  typeWf     := by apply Formula.checkWf_ok; rfl
  defEval    := by
    intrinsic_def_eval [binTerm, stringEndsWithB, stringEndsWithDefAxiom]; intros; rfl

instance : IntrinsicSound [stringEndsWith] stringEndsWith := stringEndsWithLawful.sound

end Intrinsics
end Stdlib

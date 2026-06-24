-- SUMMARY: Byte-string intrinsics (`String.length`, `cat`, `equal`, `starts_with`, `ends_with`) and soundness instances.
import Mica.Stdlib.IntStd

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

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

private def stringLengthTerm (x : Term .value) : Term .value :=
  .unop (.uninterpreted stringLengthSym.name .value .value) x

private def stringCatTerm (x y : Term .value) : Term .value :=
  .binop (.uninterpreted stringCatSym.name .value .value .value) x y

private def stringEqualTerm (x y : Term .value) : Term .value :=
  .binop (.uninterpreted stringEqualSym.name .value .value .value) x y

private def stringStartsWithTerm (x y : Term .value) : Term .value :=
  .binop (.uninterpreted stringStartsWithSym.name .value .value .value) x y

private def stringEndsWithTerm (x y : Term .value) : Term .value :=
  .binop (.uninterpreted stringEndsWithSym.name .value .value .value) x y

/-! Each intrinsic carries two axioms, both quantified over the **value sort**:
a *defining* axiom tying the symbol to Z3's native sequence theory (through the
`toString`/`toInt` projections), and a *typing* axiom asserting the result is
the expected value constructor (`is-of_int`/`is-of_string`/`is-of_bool`).

The typing axiom is what lets a bare value-level equality such as
`String.length s = 2` discharge: without it Z3 only knows the symbol's `toInt`
projection, not that the result *is* an integer value. Only the defining axiom
is written by hand here; the typing axiom is generated uniformly from the result
embedding by `Pure.Binary`/`Pure.Unary`. -/

def stringLengthDefAxiom : Formula :=
  .forall_ "s" .value [.term (stringLengthTerm (.var .value "s"))] <|
    .eq .int
      (.unop .toInt (stringLengthTerm (.var .value "s")))
      (.unop .seqLen (.unop .toString (.var .value "s")))

def stringCatDefAxiom : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (stringCatTerm (.var .value "a") (.var .value "b"))] <|
    .eq .string
      (.unop .toString (stringCatTerm (.var .value "a") (.var .value "b")))
      (.binop .seqConcat (.unop .toString (.var .value "a")) (.unop .toString (.var .value "b")))

def stringEqualDefAxiom : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (stringEqualTerm (.var .value "a") (.var .value "b"))] <|
    .eq .bool
      (.unop .toBool (stringEqualTerm (.var .value "a") (.var .value "b")))
      (.binop (.eq (τ := .string)) (.unop .toString (.var .value "a")) (.unop .toString (.var .value "b")))

def stringStartsWithDefAxiom : Formula :=
  .all "prefix" .value <| .forall_ "s" .value
    [.term (stringStartsWithTerm (.var .value "prefix") (.var .value "s"))] <|
    .eq .bool
      (.unop .toBool (stringStartsWithTerm (.var .value "prefix") (.var .value "s")))
      (.binop .seqPrefixOf (.unop .toString (.var .value "prefix")) (.unop .toString (.var .value "s")))

def stringEndsWithDefAxiom : Formula :=
  .all "suffix" .value <| .forall_ "s" .value
    [.term (stringEndsWithTerm (.var .value "suffix") (.var .value "s"))] <|
    .eq .bool
      (.unop .toBool (stringEndsWithTerm (.var .value "suffix") (.var .value "s")))
      (.binop .seqSuffixOf (.unop .toString (.var .value "suffix")) (.unop .toString (.var .value "s")))

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
  defWf      := by
    simp only [stringLengthB, Pure.Unary.toIntrinsic, Pure.Unary.sym]
    simp [stringLengthDefAxiom, stringLengthTerm, Intrinsic.sigOf, Intrinsic.foldSig,
      Formula.wfIn, Term.wfIn, UnOp.wfIn, Signature.extendWithSym, Signature.empty,
      Signature.addUnary, Signature.declVar, Signature.addVar, Signature.remove]
  typeWf     := by
    simp only [stringLengthB, Pure.Unary.typeAxiom, Pure.Unary.opTerm, Pure.Unary.toIntrinsic,
      Pure.Unary.sym, Embedding.int]
    simp [Intrinsic.sigOf, Intrinsic.foldSig, Formula.wfIn, Term.wfIn, UnOp.wfIn,
      UnPred.wfIn, Signature.extendWithSym, Signature.empty, Signature.addUnary,
      Signature.declVar, Signature.addVar, Signature.remove]
  defEval    := by
    intro ρ hρ
    simp only [Env.respects] at hρ
    simp only [stringLengthB, stringLengthDefAxiom, Formula.eval]
    intro s
    have hu : (ρ.updateConst .value "s" s).unary .value .value "string_length"
        = stringLengthSym.interp := by
      rw [Env.updateConst_unary]
      simpa [stringLengthSym, stringLengthB, Pure.Unary.sym, Embedding.str, Embedding.int] using hρ
    simp [stringLengthTerm, Term.eval, Env.lookupConst_updateConst_same, hu,
      stringLengthSym, valStr]
    rfl

instance : IntrinsicSound [stringLength] stringLength := stringLengthLawful.sound

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
  defWf      := by
    simp only [stringCatB, Pure.Binary.toIntrinsic, Pure.Binary.sym]
    simp [stringCatDefAxiom, stringCatTerm, Intrinsic.sigOf, Intrinsic.foldSig,
      Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn, Signature.extendWithSym,
      Signature.empty, Signature.addBinary, Signature.declVar, Signature.addVar,
      Signature.remove]
  typeWf     := by
    simp only [stringCatB, Pure.Binary.typeAxiom, Pure.Binary.opTerm, Pure.Binary.toIntrinsic,
      Pure.Binary.sym, Embedding.str]
    simp [Intrinsic.sigOf, Intrinsic.foldSig, Formula.wfIn, Term.wfIn, BinOp.wfIn,
      UnPred.wfIn, Signature.extendWithSym, Signature.empty, Signature.addBinary,
      Signature.declVar, Signature.addVar, Signature.remove]
  defEval    := by
    intro ρ hρ
    simp only [Env.respects] at hρ
    simp only [stringCatB, stringCatDefAxiom, Formula.all, Formula.eval]
    intro x y
    have hb : ((ρ.updateConst .value "a" x).updateConst .value "b" y).binary
        .value .value .value "string_cat" = fun a b => stringCatSym.interp (a, b) := by
      rw [Env.updateConst_binary, Env.updateConst_binary]
      simpa [stringCatSym, stringCatB, Pure.Binary.sym, Embedding.str] using hρ
    simp [stringCatTerm, Term.eval, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb, stringCatSym, valStr]
    rfl

instance : IntrinsicSound [stringCat] stringCat := stringCatLawful.sound

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
  defWf      := by
    simp only [stringEqualB, Pure.Binary.toIntrinsic, Pure.Binary.sym]
    simp [stringEqualDefAxiom, stringEqualTerm, Intrinsic.sigOf, Intrinsic.foldSig,
      Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn, Signature.extendWithSym,
      Signature.empty, Signature.addBinary, Signature.declVar, Signature.addVar,
      Signature.remove]
  typeWf     := by
    simp only [stringEqualB, Pure.Binary.typeAxiom, Pure.Binary.opTerm, Pure.Binary.toIntrinsic,
      Pure.Binary.sym, Embedding.bool]
    simp [Intrinsic.sigOf, Intrinsic.foldSig, Formula.wfIn, Term.wfIn, BinOp.wfIn,
      UnPred.wfIn, Signature.extendWithSym, Signature.empty, Signature.addBinary,
      Signature.declVar, Signature.addVar, Signature.remove]
  defEval    := by
    intro ρ hρ
    simp only [Env.respects] at hρ
    simp only [stringEqualB, stringEqualDefAxiom, Formula.all, Formula.eval]
    intro x y
    have hb : ((ρ.updateConst .value "a" x).updateConst .value "b" y).binary
        .value .value .value "string_equal" = fun a b => stringEqualSym.interp (a, b) := by
      rw [Env.updateConst_binary, Env.updateConst_binary]
      simpa [stringEqualSym, stringEqualB, Pure.Binary.sym, Embedding.str, Embedding.bool] using hρ
    simp [stringEqualTerm, Term.eval, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb, stringEqualSym, valStr,
      Bool.beq_eq_decide_eq]
    rfl

instance : IntrinsicSound [stringEqual] stringEqual := stringEqualLawful.sound

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
  defWf      := by
    simp only [stringStartsWithB, Pure.Binary.toIntrinsic, Pure.Binary.sym]
    simp [stringStartsWithDefAxiom, stringStartsWithTerm, Intrinsic.sigOf, Intrinsic.foldSig,
      Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn, Signature.extendWithSym,
      Signature.empty, Signature.addBinary, Signature.declVar, Signature.addVar,
      Signature.remove]
  typeWf     := by
    simp only [stringStartsWithB, Pure.Binary.typeAxiom, Pure.Binary.opTerm,
      Pure.Binary.toIntrinsic, Pure.Binary.sym, Embedding.bool]
    simp [Intrinsic.sigOf, Intrinsic.foldSig, Formula.wfIn, Term.wfIn, BinOp.wfIn,
      UnPred.wfIn, Signature.extendWithSym, Signature.empty, Signature.addBinary,
      Signature.declVar, Signature.addVar, Signature.remove]
  defEval    := by
    intro ρ hρ
    simp only [Env.respects] at hρ
    simp only [stringStartsWithB, stringStartsWithDefAxiom, Formula.all, Formula.eval]
    intro x y
    have hb : ((ρ.updateConst .value "prefix" x).updateConst .value "s" y).binary
        .value .value .value "string_starts_with"
        = fun a b => stringStartsWithSym.interp (a, b) := by
      rw [Env.updateConst_binary, Env.updateConst_binary]
      simpa [stringStartsWithSym, stringStartsWithB, Pure.Binary.sym, Embedding.str,
        Embedding.bool] using hρ
    simp [stringStartsWithTerm, Term.eval, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "prefix" ≠ "s" by decide), hb,
      stringStartsWithSym, valStr]
    rfl

instance : IntrinsicSound [stringStartsWith] stringStartsWith := stringStartsWithLawful.sound

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
  defWf      := by
    simp only [stringEndsWithB, Pure.Binary.toIntrinsic, Pure.Binary.sym]
    simp [stringEndsWithDefAxiom, stringEndsWithTerm, Intrinsic.sigOf, Intrinsic.foldSig,
      Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn, Signature.extendWithSym,
      Signature.empty, Signature.addBinary, Signature.declVar, Signature.addVar,
      Signature.remove]
  typeWf     := by
    simp only [stringEndsWithB, Pure.Binary.typeAxiom, Pure.Binary.opTerm,
      Pure.Binary.toIntrinsic, Pure.Binary.sym, Embedding.bool]
    simp [Intrinsic.sigOf, Intrinsic.foldSig, Formula.wfIn, Term.wfIn, BinOp.wfIn,
      UnPred.wfIn, Signature.extendWithSym, Signature.empty, Signature.addBinary,
      Signature.declVar, Signature.addVar, Signature.remove]
  defEval    := by
    intro ρ hρ
    simp only [Env.respects] at hρ
    simp only [stringEndsWithB, stringEndsWithDefAxiom, Formula.all, Formula.eval]
    intro x y
    have hb : ((ρ.updateConst .value "suffix" x).updateConst .value "s" y).binary
        .value .value .value "string_ends_with"
        = fun a b => stringEndsWithSym.interp (a, b) := by
      rw [Env.updateConst_binary, Env.updateConst_binary]
      simpa [stringEndsWithSym, stringEndsWithB, Pure.Binary.sym, Embedding.str,
        Embedding.bool] using hρ
    simp [stringEndsWithTerm, Term.eval, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "suffix" ≠ "s" by decide), hb,
      stringEndsWithSym, valStr]
    rfl

instance : IntrinsicSound [stringEndsWith] stringEndsWith := stringEndsWithLawful.sound

end Intrinsics
end Stdlib

-- SUMMARY: Byte-string intrinsics (`String.length`, `get`, `sub`, `cat`, `equal`, `starts_with`, `ends_with`) and soundness instances.
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

/-- FOL symbol for `String.get`. -/
def stringGetSym : FOL.Symbol .two where
  name   := "string_get"
  interp := fun (s, i) => .char ((valStr s)[Int.toNat (valInt i)]?.getD 0)

/-- Total byte-string slice used by the FOL interpretation. The intrinsic
    precondition restricts runtime calls to OCaml's in-bounds case. -/
def stringSubBytes (s : List UInt8) (pos len : Int) : List UInt8 :=
  (s.drop (Int.toNat pos)).take (Int.toNat len)

/-- FOL symbol for `String.sub`. -/
def stringSubSym : FOL.Symbol .three where
  name   := "string_sub"
  interp := fun (s, pos, len) => .str (stringSubBytes (valStr s) (valInt pos) (valInt len))

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
@[simp] theorem stringGetSym_name : stringGetSym.name = "string_get" := rfl
@[simp] theorem stringSubSym_name : stringSubSym.name = "string_sub" := rfl
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

/-- The FOL precondition of `String.get`, as a function of the argument names. -/
def stringGetPre (s i : String) : Formula :=
  let idx := .unop .toInt (.var .value i)
  let len := .unop .seqLen (.unop .toString (.var .value s))
  .and
    (.binpred .le (.const (.i 0)) idx)
    (.binpred .lt idx len)

/-- The value-level FOL term for `String.get s i`. -/
def stringGetTerm (s i : Term .value) : Term .value :=
  binTerm "string_get" s i

/-- Total byte lookup used by the FOL interpretation. The intrinsic precondition
    restricts runtime calls to OCaml's in-bounds case. -/
def stringGetByte (s : List UInt8) (i : Int) : UInt8 :=
  s[Int.toNat i]?.getD 0

def stringGetDefAxiom : Formula :=
  .all "s" .value <| .forall_ "i" .value
    [.term (stringGetTerm (.var .value "s") (.var .value "i"))] <|
    .implies (stringGetPre "s" "i") <|
      .eq .char
        (.unop .toChar (stringGetTerm (.var .value "s") (.var .value "i")))
        (.binop .seqNth (.unop .toString (.var .value "s")) (.unop .toInt (.var .value "i")))

/-- The FOL precondition of `String.sub`, as a function of the argument names. -/
def stringSubPre (s pos len : String) : Formula :=
  let p := .unop .toInt (.var .value pos)
  let l := .unop .toInt (.var .value len)
  let strlen := .unop .seqLen (.unop .toString (.var .value s))
  .and
    (.binpred .le (.const (.i 0)) p)
    (.and
      (.binpred .le (.const (.i 0)) l)
      (.binpred .le (.binop .add p l) strlen))

/-- The value-level FOL term for `String.sub s pos len`. -/
def stringSubTerm (s pos len : Term .value) : Term .value :=
  terTerm "string_sub" s pos len

def stringSubDefAxiom : Formula :=
  .all "s" .value <| .all "pos" .value <| .forall_ "len" .value
    [.term (stringSubTerm (.var .value "s") (.var .value "pos") (.var .value "len"))] <|
    .implies (stringSubPre "s" "pos" "len") <|
      .eq .string
        (.unop .toString (stringSubTerm (.var .value "s") (.var .value "pos") (.var .value "len")))
        (.terop .seqExtract
          (.unop .toString (.var .value "s"))
          (.unop .toInt (.var .value "pos"))
          (.unop .toInt (.var .value "len")))

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
  dom      := fun _ => True
  pre      := none
  defAxiom := stringLengthDefAxiom

def stringLength : Intrinsic := stringLengthB.toIntrinsic

@[simp] theorem stringLength_arity : stringLength.arity = .one := rfl
@[simp] theorem stringLength_folSym : stringLength.folSym = some stringLengthSym := rfl

def stringLengthLawful : stringLengthB.Lawful where
  argL         := Embedding.lawfulStr
  resL         := Embedding.lawfulInt
  domSound     := fun _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ => .rfl
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by intrinsic_def_eval [unTerm, stringLengthB, stringLengthDefAxiom]; intros; rfl

instance : IntrinsicSound [stringLength] stringLength := stringLengthLawful.sound

/-! ## `String.cat` -/

/-- `String.cat`: byte-string concatenation, built by `Pure.Binary`. -/
def stringCatB : Pure.Binary where
  name     := "string_cat"
  path     := some ("String", ["cat"])
  arg₁     := .str
  arg₂     := .str
  res      := .str
  f        := (fun x y => x ++ y : List UInt8 → List UInt8 → List UInt8)
  dom      := fun _ _ => True
  pre      := none
  defAxiom := stringCatDefAxiom

def stringCat : Intrinsic := stringCatB.toIntrinsic

@[simp] theorem stringCat_arity : stringCat.arity = .two := rfl
@[simp] theorem stringCat_folSym : stringCat.folSym = some stringCatSym := rfl

def stringCatLawful : stringCatB.Lawful where
  argL₁        := Embedding.lawfulStr
  argL₂        := Embedding.lawfulStr
  resL         := Embedding.lawfulStr
  domSound     := fun _ _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ _ => sep_emp.1
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by intrinsic_def_eval [binTerm, stringCatB, stringCatDefAxiom]; intros; rfl

instance : IntrinsicSound [stringCat] stringCat := stringCatLawful.sound

/-! ## `String.get` -/

/-- `String.get`: byte lookup, with OCaml's in-bounds precondition. -/
def stringGetB : Pure.Binary where
  name     := "string_get"
  path     := some ("String", ["get"])
  arg₁     := .str
  arg₂     := .int
  res      := .char
  f        := stringGetByte
  dom      := (fun s i => 0 ≤ i ∧ i < (s.length : Int) : List UInt8 → Int → Prop)
  pre      := some stringGetPre
  defAxiom := stringGetDefAxiom

def stringGet : Intrinsic := stringGetB.toIntrinsic

@[simp] theorem stringGet_arity : stringGet.arity = .two := rfl
@[simp] theorem stringGet_folSym : stringGet.folSym = some stringGetSym := rfl

def stringGetLawful : stringGetB.Lawful where
  argL₁        := Embedding.lawfulStr
  argL₂        := Embedding.lawfulInt
  resL         := Embedding.lawfulChar
  domSound     := by
    intro ρ s i h
    have hpre := h stringGetPre rfl
    simpa [stringGetB, stringGetPre, Embedding.str, Embedding.int, Formula.eval, Term.eval,
      Const.denote, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), valStr, valInt] using hpre
  semWellTyped := fun _ _ _ _ _ => sep_emp.1
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by
    have hsym : stringGetB.sym = stringGetSym := rfl
    intro ρ hresp
    rw [hsym] at hresp
    simp only [stringGetB, stringGetDefAxiom, Formula.all, Formula.eval]
    intro s i hpre
    have hbin : (((ρ.updateConst .value "s" s).updateConst .value "i" i).binary
        .value .value .value "string_get") = fun a b => stringGetSym.interp (a, b) := by
      rw [Env.updateConst_binary, Env.updateConst_binary]
      simpa [Env.respects, stringGetSym] using hresp
    simp [stringGetTerm, binTerm, stringGetSym, hbin,
      Term.eval, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "s" ≠ "i" by decide), valStr, valInt]
    rfl

instance : IntrinsicSound [stringGet] stringGet := stringGetLawful.sound

/-! ## `String.sub` -/

/-- `String.sub`: byte-string slicing, with OCaml's bounds precondition. -/
def stringSubB : Pure.Ternary where
  name     := "string_sub"
  path     := some ("String", ["sub"])
  arg₁     := .str
  arg₂     := .int
  arg₃     := .int
  res      := .str
  f        := stringSubBytes
  dom      := (fun s pos len => 0 ≤ pos ∧ 0 ≤ len ∧ pos + len ≤ (s.length : Int) :
                List UInt8 → Int → Int → Prop)
  pre      := some stringSubPre
  defAxiom := stringSubDefAxiom

def stringSub : Intrinsic := stringSubB.toIntrinsic

@[simp] theorem stringSub_arity : stringSub.arity = .three := rfl
@[simp] theorem stringSub_folSym : stringSub.folSym = some stringSubSym := rfl

def stringSubLawful : stringSubB.Lawful where
  argL₁        := Embedding.lawfulStr
  argL₂        := Embedding.lawfulInt
  argL₃        := Embedding.lawfulInt
  resL         := Embedding.lawfulStr
  domSound     := by
    intro ρ s pos len h
    have hpre := h stringSubPre rfl
    simpa [stringSubB, stringSubPre, Embedding.str, Embedding.int, Formula.eval, Term.eval,
      Const.denote, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide),
      Env.lookupConst_updateConst_ne (show "a" ≠ "c" by decide),
      Env.lookupConst_updateConst_ne (show "b" ≠ "c" by decide), valStr, valInt] using hpre
  semWellTyped := fun _ _ _ _ _ _ => emp_sep.1.trans emp_sep.1
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by
    have hsym : stringSubB.sym = stringSubSym := rfl
    intro ρ hresp
    rw [hsym] at hresp
    simp only [stringSubB, stringSubDefAxiom, Formula.all, Formula.eval]
    intro s pos len hpre
    have hter : ((((ρ.updateConst .value "s" s).updateConst .value "pos" pos).updateConst
          .value "len" len).ternary .value .value .value .value "string_sub") =
        fun a b c => stringSubSym.interp (a, b, c) := by
      rw [Env.updateConst_ternary, Env.updateConst_ternary, Env.updateConst_ternary]
      simpa [Env.respects, stringSubSym] using hresp
    simp [stringSubTerm, terTerm, stringSubSym, stringSubBytes, hter, Term.eval,
      Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "s" ≠ "pos" by decide),
      Env.lookupConst_updateConst_ne (show "s" ≠ "len" by decide),
      Env.lookupConst_updateConst_ne (show "pos" ≠ "len" by decide),
      valStr, valInt]
    rfl

instance : IntrinsicSound [stringSub] stringSub := stringSubLawful.sound

/-! ## `String.equal` -/

/-- `String.equal`: byte-string equality, built by `Pure.Binary`. -/
def stringEqualB : Pure.Binary where
  name     := "string_equal"
  path     := some ("String", ["equal"])
  arg₁     := .str
  arg₂     := .str
  res      := .bool
  f        := (fun x y => x == y : List UInt8 → List UInt8 → Bool)
  dom      := fun _ _ => True
  pre      := none
  defAxiom := stringEqualDefAxiom

def stringEqual : Intrinsic := stringEqualB.toIntrinsic

@[simp] theorem stringEqual_arity : stringEqual.arity = .two := rfl
@[simp] theorem stringEqual_folSym : stringEqual.folSym = some stringEqualSym := rfl

def stringEqualLawful : stringEqualB.Lawful where
  argL₁        := Embedding.lawfulStr
  argL₂        := Embedding.lawfulStr
  resL         := Embedding.lawfulBool
  domSound     := fun _ _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ _ => sep_emp.1
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by
    intrinsic_def_eval [binTerm, stringEqualB, stringEqualDefAxiom, Bool.beq_eq_decide_eq]
    intros; rfl

instance : IntrinsicSound [stringEqual] stringEqual := stringEqualLawful.sound

/-! ## `String.starts_with` -/

/-- `String.starts_with`: byte-string prefix test, built by `Pure.Binary`. -/
def stringStartsWithB : Pure.Binary where
  name     := "string_starts_with"
  path     := some ("String", ["starts_with"])
  arg₁     := .str
  arg₂     := .str
  res      := .bool
  f        := (fun x y => x.isPrefixOf y : List UInt8 → List UInt8 → Bool)
  dom      := fun _ _ => True
  pre      := none
  defAxiom := stringStartsWithDefAxiom

def stringStartsWith : Intrinsic := stringStartsWithB.toIntrinsic

@[simp] theorem stringStartsWith_arity : stringStartsWith.arity = .two := rfl
@[simp] theorem stringStartsWith_folSym :
    stringStartsWith.folSym = some stringStartsWithSym := rfl

def stringStartsWithLawful : stringStartsWithB.Lawful where
  argL₁        := Embedding.lawfulStr
  argL₂        := Embedding.lawfulStr
  resL         := Embedding.lawfulBool
  domSound     := fun _ _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ _ => sep_emp.1
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by
    intrinsic_def_eval [binTerm, stringStartsWithB, stringStartsWithDefAxiom]; intros; rfl

instance : IntrinsicSound [stringStartsWith] stringStartsWith := stringStartsWithLawful.sound

/-! ## `String.ends_with` -/

/-- `String.ends_with`: byte-string suffix test, built by `Pure.Binary`. -/
def stringEndsWithB : Pure.Binary where
  name     := "string_ends_with"
  path     := some ("String", ["ends_with"])
  arg₁     := .str
  arg₂     := .str
  res      := .bool
  f        := (fun x y => x.isSuffixOf y : List UInt8 → List UInt8 → Bool)
  dom      := fun _ _ => True
  pre      := none
  defAxiom := stringEndsWithDefAxiom

def stringEndsWith : Intrinsic := stringEndsWithB.toIntrinsic

@[simp] theorem stringEndsWith_arity : stringEndsWith.arity = .two := rfl
@[simp] theorem stringEndsWith_folSym : stringEndsWith.folSym = some stringEndsWithSym := rfl

def stringEndsWithLawful : stringEndsWithB.Lawful where
  argL₁        := Embedding.lawfulStr
  argL₂        := Embedding.lawfulStr
  resL         := Embedding.lawfulBool
  domSound     := fun _ _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ _ => sep_emp.1
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by
    intrinsic_def_eval [binTerm, stringEndsWithB, stringEndsWithDefAxiom]; intros; rfl

instance : IntrinsicSound [stringEndsWith] stringEndsWith := stringEndsWithLawful.sound

end Intrinsics
end Stdlib

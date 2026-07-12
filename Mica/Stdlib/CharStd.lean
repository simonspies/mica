-- SUMMARY: Character intrinsics (`Char.code`, `Char.chr`, `Char.equal`) and their soundness instances.
import Mica.Stdlib.IntStd

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## FOL symbols -/

/-- FOL symbol for `Char.code`. -/
def charCodeSym : FOL.Symbol .one where
  name   := "char_code"
  interp := fun a => .int (valChar a).toNat

/-- FOL-level result of `Char.chr`: agree with byte conversion on OCaml's
    valid range, and return zero outside it. -/
def charChrByte (n : Int) : UInt8 :=
  if n ≥ 0 then
    if n < 256 then UInt8.ofNat n.toNat else 0
  else 0

/-- FOL symbol for `Char.chr`. -/
def charChrSym : FOL.Symbol .one where
  name   := "char_chr"
  interp := fun a => .char (charChrByte (valInt a))

/-- FOL symbol for `Char.equal`. -/
def charEqualSym : FOL.Symbol .two where
  name   := "char_equal"
  interp := fun (a, b) => .bool (valChar a == valChar b)

@[simp] theorem charCodeSym_name : charCodeSym.name = "char_code" := rfl
@[simp] theorem charChrSym_name : charChrSym.name = "char_chr" := rfl
@[simp] theorem charEqualSym_name : charEqualSym.name = "char_equal" := rfl

/-! ## `Char.code` -/

def charCodeDefAxiom : Formula :=
  .forall_ "c" .value [.term (unTerm "char_code" (.var .value "c"))] <|
    .eq .int
      (.unop .toInt (unTerm "char_code" (.var .value "c")))
      (.unop .charToInt (.unop .toChar (.var .value "c")))

/-- `Char.code`: byte value as an integer. -/
def charCodeB : Pure.Unary where
  name     := "char_code"
  path     := some ("Char", ["code"])
  arg      := .char
  res      := .int
  f        := (fun c => (c.toNat : Int) : UInt8 → Int)
  dom      := fun _ => True
  pre      := none
  defAxiom := charCodeDefAxiom

def charCode : Intrinsic := charCodeB.toIntrinsic

@[simp] theorem charCode_arity : charCode.arity = .one := rfl
@[simp] theorem charCode_folSym : charCode.folSym = some charCodeSym := rfl

def charCodeLawful : charCodeB.Lawful where
  argL         := Embedding.lawfulChar
  resL         := Embedding.lawfulInt
  domSound     := fun _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ => .rfl
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by
    intrinsic_def_eval [unTerm, charCodeB, charCodeDefAxiom]
    intro v
    rfl

instance : IntrinsicSound [charCode] charCode := charCodeLawful.sound

/-! ## `Char.chr` -/

/-- The FOL precondition of `Char.chr`, as a function of the argument name. -/
def charChrPre (n : String) : Formula :=
  let t := .unop .toInt (.var .value n)
  .and
    (.binpred .le (.const (.i 0)) t)
    (.binpred .lt t (.const (.i 256)))

def charChrDefAxiom : Formula :=
  .forall_ "n" .value [.term (unTerm "char_chr" (.var .value "n"))] <|
    .implies (charChrPre "n") <|
      .eq .char
        (.unop .toChar (unTerm "char_chr" (.var .value "n")))
        (.unop .intToChar (.unop .toInt (.var .value "n")))

/-- `Char.chr`: integer to byte, with the OCaml precondition `0 <= n < 256`.
    The defining axiom only constrains the valid range, matching the spec
    precondition that rules out OCaml's raising cases. -/
def charChrB : Pure.Unary where
  name     := "char_chr"
  path     := some ("Char", ["chr"])
  arg      := .int
  res      := .char
  f        := charChrByte
  dom      := (fun n => 0 ≤ n ∧ n < 256 : Int → Prop)
  pre      := some charChrPre
  defAxiom := charChrDefAxiom

def charChr : Intrinsic := charChrB.toIntrinsic

@[simp] theorem charChr_arity : charChr.arity = .one := rfl
@[simp] theorem charChr_folSym : charChr.folSym = some charChrSym := rfl

def charChrLawful : charChrB.Lawful where
  argL         := Embedding.lawfulInt
  resL         := Embedding.lawfulChar
  domSound     := by
    intro ρ n h
    have hpre := h charChrPre rfl
    simpa [charChrB, charChrPre, Embedding.int, Formula.eval, Term.eval, Const.denote,
      Env.lookupConst_updateConst_same, valInt] using hpre
  semWellTyped := fun _ _ _ _ => .rfl
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by
    have hsym : charChrB.sym = charChrSym := rfl
    intro ρ hresp
    rw [hsym] at hresp
    simp only [charChrB, charChrDefAxiom, Formula.eval]
    intro x hpre
    have hun : (ρ.updateConst .value "n" x).unary .value .value "char_chr" =
        charChrSym.interp := by
      rw [Env.updateConst_unary]
      simpa [Env.respects] using hresp
    have hbounds : 0 ≤ valInt x ∧ valInt x < 256 := by
      simpa [charChrPre, Formula.eval, Term.eval, Const.denote,
        Env.lookupConst_updateConst_same, valInt] using hpre
    simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hun, charChrSym]
    cases x <;> simp [valInt, charChrByte] at hbounds ⊢
    rw [if_pos hbounds.1, if_pos hbounds.2, Int.emod_eq_of_lt hbounds.1 hbounds.2]

instance : IntrinsicSound [charChr] charChr := charChrLawful.sound

/-! ## `Char.equal` -/

def charEqualDefAxiom : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm "char_equal" (.var .value "a") (.var .value "b"))] <|
    .eq .bool
      (.unop .toBool (binTerm "char_equal" (.var .value "a") (.var .value "b")))
      (.binop (.eq (τ := .char)) (.unop .toChar (.var .value "a")) (.unop .toChar (.var .value "b")))

/-- `Char.equal`: byte equality. -/
def charEqualB : Pure.Binary where
  name     := "char_equal"
  path     := some ("Char", ["equal"])
  arg₁     := .char
  arg₂     := .char
  res      := .bool
  f        := (fun x y => x == y : UInt8 → UInt8 → Bool)
  dom      := fun _ _ => True
  pre      := none
  defAxiom := charEqualDefAxiom

def charEqual : Intrinsic := charEqualB.toIntrinsic

@[simp] theorem charEqual_arity : charEqual.arity = .two := rfl
@[simp] theorem charEqual_folSym : charEqual.folSym = some charEqualSym := rfl

def charEqualLawful : charEqualB.Lawful where
  argL₁        := Embedding.lawfulChar
  argL₂        := Embedding.lawfulChar
  resL         := Embedding.lawfulBool
  domSound     := fun _ _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ _ => sep_emp.1
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by
    intrinsic_def_eval [binTerm, charEqualB, charEqualDefAxiom, Bool.beq_eq_decide_eq]
    intros; rfl

instance : IntrinsicSound [charEqual] charEqual := charEqualLawful.sound

end Intrinsics
end Stdlib

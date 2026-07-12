-- SUMMARY: Immutable-vector intrinsics (`Vec.length`, `Vec.get`, `Vec.set`, `Vec.make`) as builder instances over the vec/poly embeddings.
import Mica.Stdlib.Combinators

open Iris Iris.BI

/-!
# Vectors

Each intrinsic gets an uninterpreted **value-sorted** FOL symbol, whose defining
axiom says it implements the corresponding interpreted `Vec`-sorted operation:

    val_vec_get : Value × Value → Value   (the symbol, declared from the signature)
    vec_get     : Vec × Int → Value       (the operation, declared in the preamble)

The symbol is what the relational encoding needs in order to translate a
spec-level `Vec.get v i`. The defining axiom then hands the solver the
operation's meaning. The axioms are unguarded: the operations are total and the
standard interpretations agree with them everywhere, not only in bounds.
The SMT preamble only constrains the underlying vector operations on their
intrinsic domains; their out-of-domain SMT values remain unspecified.

`get`/`set` are partial: their `dom` demands an in-bounds index, so an
out-of-bounds call is stuck, and the `pre` precondition is what makes the
weakest precondition provable at a call site. `make` demands a nonnegative
length. Polymorphism is carried by the `Embedding.vec`/`Embedding.poly`
embeddings, whose type predicates (big-sep of element typings, resp. the
typing fact itself) feed the `semWellTyped` obligations.
-/

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## Shared term abbreviations -/

/-- The vector argument `name`, projected out of its `Value` wrapper. -/
private def vecOf (name : String) : Term .vec := .unop .toVec (.var .value name)

/-- The integer argument `name`, projected out of its `Value` wrapper. -/
private def intOf (name : String) : Term .int := .unop .toInt (.var .value name)

/-- `0 ≤ i < vec_length v`: the in-bounds precondition shared by `get` and `set`. -/
private def vecBoundsPre (v i : String) : Formula :=
  .and
    (.binpred .le (.const (.i 0)) (intOf i))
    (.binpred .lt (intOf i) (.unop .vecLen (vecOf v)))

/-! ## Defining axioms

Each says the value-sorted symbol implements the `Vec`-sorted operation on the
projections of its arguments. Unguarded, and valid for every value. -/

def vecLengthDefAxiom : Formula :=
  .forall_ "v" .value [.term (unTerm "val_vec_length" (.var .value "v"))] <|
    .eq .int
      (.unop .toInt (unTerm "val_vec_length" (.var .value "v")))
      (.unop .vecLen (vecOf "v"))

def vecGetDefAxiom : Formula :=
  .all "v" .value <| .forall_ "i" .value
    [.term (binTerm "val_vec_get" (.var .value "v") (.var .value "i"))] <|
    .eq .value
      (binTerm "val_vec_get" (.var .value "v") (.var .value "i"))
      (.binop .vecGet (vecOf "v") (intOf "i"))

def vecSetDefAxiom : Formula :=
  .all "v" .value <| .all "i" .value <| .forall_ "x" .value
    [.term (terTerm "val_vec_set" (.var .value "v") (.var .value "i") (.var .value "x"))] <|
    .eq .value
      (terTerm "val_vec_set" (.var .value "v") (.var .value "i") (.var .value "x"))
      (.unop .ofVec (.terop .vecSet (vecOf "v") (intOf "i") (.var .value "x")))

def vecMakeDefAxiom : Formula :=
  .all "n" .value <| .forall_ "x" .value
    [.term (binTerm "val_vec_make" (.var .value "n") (.var .value "x"))] <|
    .eq .value
      (binTerm "val_vec_make" (.var .value "n") (.var .value "x"))
      (.unop .ofVec (.binop .vecMake (intOf "n") (.var .value "x")))

/-! ## `Vec.length` -/

/-- `Vec.length : 'a vec -> int`. Total. -/
def vecLengthB : Pure.Unary where
  name     := "val_vec_length"
  path     := some ("Vec", ["length"])
  arg      := .vec
  res      := .int
  f        := (fun l => (l.length : Int) : List Runtime.Val → Int)
  dom      := fun _ => True
  pre      := none
  typing   := fun _ tys =>
    match tys with
    | [.vec t] => .ok [("a", t)]
    | [_] => .error "Vec.length expects a vector argument"
    | _ => .error s!"expected 1 argument, got {tys.length}"
  defAxiom := vecLengthDefAxiom

def vecLength : Intrinsic := vecLengthB.toIntrinsic

@[simp] theorem vecLength_arity : vecLength.arity = .one := rfl
@[simp] theorem vecLength_folSym : vecLength.folSym = some vecLengthB.sym := rfl
@[simp] theorem vecLengthSym_name : vecLengthB.sym.name = "val_vec_length" := rfl

def vecLengthLawful : vecLengthB.Lawful where
  argL         := Embedding.lawfulVec
  resL         := Embedding.lawfulInt
  domSound     := fun _ _ _ => True.intro
  semWellTyped := fun _ _ _ _ => affine
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by
    intrinsic_def_eval [unTerm, vecOf, UnOp.eval, vecLengthB, vecLengthDefAxiom]
    intro v
    rfl

instance : IntrinsicSound [vecLength] vecLength := vecLengthLawful.sound

/-! ## `Vec.get` -/

/-- `Vec.get : 'a vec -> int -> 'a`. Partial: the index must be in bounds. -/
def vecGetB : Pure.Binary where
  name     := "val_vec_get"
  path     := some ("Vec", ["get"])
  arg₁     := .vec
  arg₂     := .int
  res      := .poly
  f        := fun (l : List Runtime.Val) (i : Int) =>
    if 0 ≤ i then (l[i.toNat]?).getD .unit else .unit
  dom      := (fun l n => 0 ≤ n ∧ n < (l.length : Int) : List Runtime.Val → Int → Prop)
  pre      := some vecBoundsPre
  typing   := fun _ tys =>
    match tys with
    | [.vec t, _] => .ok [("a", t)]
    | [_, _] => .error "Vec.get expects a vector as its first argument"
    | _ => .error s!"expected 2 arguments, got {tys.length}"
  defAxiom := vecGetDefAxiom

def vecGet : Intrinsic := vecGetB.toIntrinsic

@[simp] theorem vecGet_arity : vecGet.arity = .two := rfl
@[simp] theorem vecGet_folSym : vecGet.folSym = some vecGetB.sym := rfl
@[simp] theorem vecGetSym_name : vecGetB.sym.name = "val_vec_get" := rfl

def vecGetLawful : vecGetB.Lawful where
  argL₁        := Embedding.lawfulVec
  argL₂        := Embedding.lawfulInt
  resL         := Embedding.lawfulPoly
  domSound     := by
    intro ρ l n h
    have hpre := h vecBoundsPre rfl
    simpa [vecGetB, vecBoundsPre, vecOf, intOf, Embedding.vec, Embedding.int,
      Formula.eval, Term.eval, Const.denote, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), valVec, valInt] using hpre
  semWellTyped := by
    refine fun σ Θ (l : List Runtime.Val) (n : Int) hdom => ?_
    obtain ⟨h0, hlen⟩ := hdom
    have hlt : n.toNat < l.length := by omega
    have hget : l[n.toNat]? = some l[n.toNat] := List.getElem?_eq_getElem hlt
    simp only [Embedding.vec, Embedding.int, Embedding.poly, vecGetB, if_pos h0,
      hget, Option.getD_some]
    refine sep_emp.1.trans ?_
    exact BigSepL.bigSepL_lookup (Φ := fun _ w => TinyML.ValHasType Θ w (σ "a")) hget
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; exact nomatch h
  defEval      := by
    intrinsic_def_eval [binTerm, vecOf, intOf, UnOp.eval, BinOp.eval, vecGetB, vecGetDefAxiom]
    intros
    rfl

instance : IntrinsicSound [vecGet] vecGet := vecGetLawful.sound

/-! ## `Vec.set` -/

/-- `Vec.set : 'a vec -> int -> 'a -> 'a vec`, the copying functional update.
    Partial: the index must be in bounds. -/
def vecSetB : Pure.Ternary where
  name     := "val_vec_set"
  path     := some ("Vec", ["set"])
  arg₁     := .vec
  arg₂     := .int
  arg₃     := .poly
  res      := .vec
  f        := fun (l : List Runtime.Val) (i : Int) (x : Runtime.Val) =>
    if 0 ≤ i then l.set i.toNat x else l
  dom      := (fun l n _ => 0 ≤ n ∧ n < (l.length : Int) :
                List Runtime.Val → Int → Runtime.Val → Prop)
  pre      := some fun v i _ => vecBoundsPre v i
  typing   := fun _ tys =>
    match tys with
    | [.vec t, _, _] => .ok [("a", t)]
    | [_, _, _] => .error "Vec.set expects a vector as its first argument"
    | _ => .error s!"expected 3 arguments, got {tys.length}"
  defAxiom := vecSetDefAxiom

def vecSet : Intrinsic := vecSetB.toIntrinsic

@[simp] theorem vecSet_arity : vecSet.arity = .three := rfl
@[simp] theorem vecSet_folSym : vecSet.folSym = some vecSetB.sym := rfl
@[simp] theorem vecSetSym_name : vecSetB.sym.name = "val_vec_set" := rfl

def vecSetLawful : vecSetB.Lawful where
  argL₁        := Embedding.lawfulVec
  argL₂        := Embedding.lawfulInt
  argL₃        := Embedding.lawfulPoly
  resL         := Embedding.lawfulVec
  domSound     := by
    intro ρ l n x h
    have hpre := h _ rfl
    simpa [vecSetB, vecBoundsPre, vecOf, intOf, Embedding.vec, Embedding.int, Embedding.poly,
      Formula.eval, Term.eval, Const.denote, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide),
      Env.lookupConst_updateConst_ne (show "a" ≠ "c" by decide),
      Env.lookupConst_updateConst_ne (show "b" ≠ "c" by decide), valVec, valInt] using hpre
  semWellTyped := by
    refine fun σ Θ (l : List Runtime.Val) (n : Int) (x : Runtime.Val) hdom => ?_
    obtain ⟨h0, hlen⟩ := hdom
    have hlt : n.toNat < l.length := by omega
    have hget : l[n.toNat]? = some l[n.toNat] := List.getElem?_eq_getElem hlt
    simp only [Embedding.vec, Embedding.int, Embedding.poly, vecSetB, if_pos h0]
    refine (sep_mono_right emp_sep.1).trans ?_
    refine (sep_mono_left (BigSepL.bigSepL_insert_acc
      (Φ := fun _ w => TinyML.ValHasType Θ w (σ "a")) hget)).trans ?_
    refine (sep_mono_left sep_elim_right).trans ?_
    exact (sep_mono_left (forall_elim x)).trans wand_elim_left
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by
    intrinsic_def_eval [terTerm, vecOf, intOf, UnOp.eval, TerOp.eval, vecSetB, vecSetDefAxiom]
    intros
    rfl

instance : IntrinsicSound [vecSet] vecSet := vecSetLawful.sound

/-! ## `Vec.make` -/

/-- `Vec.make : int -> 'a -> 'a vec`. Partial: the length must be nonnegative. -/
def vecMakeB : Pure.Binary where
  name     := "val_vec_make"
  path     := some ("Vec", ["make"])
  arg₁     := .int
  arg₂     := .poly
  res      := .vec
  f        := fun (m : Int) (x : Runtime.Val) =>
    let len := m
    if 0 ≤ len then List.replicate len.toNat x else []
  dom      := (fun m _ => 0 ≤ m : Int → Runtime.Val → Prop)
  pre      := some fun n _ => .binpred .le (.const (.i 0)) (intOf n)
  typing   := fun _ tys =>
    match tys with
    | [_, t] => .ok [("a", t)]
    | _ => .error s!"expected 2 arguments, got {tys.length}"
  defAxiom := vecMakeDefAxiom

def vecMake : Intrinsic := vecMakeB.toIntrinsic

@[simp] theorem vecMake_arity : vecMake.arity = .two := rfl
@[simp] theorem vecMake_folSym : vecMake.folSym = some vecMakeB.sym := rfl
@[simp] theorem vecMakeSym_name : vecMakeB.sym.name = "val_vec_make" := rfl

def vecMakeLawful : vecMakeB.Lawful where
  argL₁        := Embedding.lawfulInt
  argL₂        := Embedding.lawfulPoly
  resL         := Embedding.lawfulVec
  domSound     := by
    intro ρ m x h
    have hpre := h _ rfl
    simpa [vecMakeB, intOf, Embedding.int, Embedding.poly, Formula.eval, Term.eval,
      Const.denote, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), valInt] using hpre
  semWellTyped := by
    refine fun σ Θ (m : Int) (x : Runtime.Val) hdom => ?_
    have hnonneg : 0 ≤ m := hdom
    simp only [Embedding.vec, Embedding.int, Embedding.poly, vecMakeB, if_pos hnonneg]
    refine emp_sep.1.trans ?_
    refine (TinyML.ValHasType.vec_replicate Θ m.toNat x (σ "a")).trans ?_
    refine (TinyML.ValHasType.vec Θ _ (σ "a")).1.trans ?_
    istart
    iintro ⟨%vs, %hv, Hs⟩
    obtain rfl : List.replicate m.toNat x = vs := by injection hv
    iexact Hs
  specBaseWf   := by apply PredTrans.checkWf_ok; rfl
  defWf        := by apply Formula.checkWf_ok; rfl
  typeWf       := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval      := by
    intrinsic_def_eval [binTerm, vecOf, intOf, UnOp.eval, BinOp.eval, vecMakeB, vecMakeDefAxiom]
    intros
    rfl

instance : IntrinsicSound [vecMake] vecMake := vecMakeLawful.sound

end Intrinsics

end Stdlib

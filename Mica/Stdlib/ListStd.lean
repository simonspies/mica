-- SUMMARY: Canonical list representation and polymorphic List intrinsics.
import Mica.Stdlib.Combinators

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

theorem valHasType_list_unfold [MicaGS HasLC.hasLC Sig]
    (W : TinyML.World) (v : Runtime.Val) (t : TinyML.Typ) :
    TinyML.ValHasType W v (.list t) ⊣⊢
      TinyML.ValHasType W v (.sum [.unit, .tuple [t, .list t]]) := by
  apply TinyML.ValHasType.named_of_unfold
  simp [TinyML.Typ.list, TinyML.Typ.predef, TinyML.TypeName.unfold,
    TinyML.Predef.arity, TinyML.Predef.decl, TinyML.Predef.tparams,
    TinyML.Predef.ctors, TinyML.DataDecl.instantiate, TinyML.Typ.subst]

/-- Runtime representation of the predefined empty list. -/
def listNil : Runtime.Val := .inj 0 2 .unit

/-- Runtime representation of predefined list cons. -/
def listCons (head tail : Runtime.Val) : Runtime.Val :=
  .inj 1 2 (.tuple [head, tail])

theorem valHasType_list_nil [MicaGS HasLC.hasLC Sig]
    (W : TinyML.World) (t : TinyML.Typ) :
    ⊢ TinyML.ValHasType W listNil (.list t) := by
  exact (TinyML.ValHasType.unit_intro W).trans
    ((TinyML.ValHasType.inj (tag := 0) (arity := 2) (s := .unit)
      (ts := [.unit, .tuple [t, .list t]]) (by simp) (by simp)).trans
      (valHasType_list_unfold W listNil t).2)

theorem valHasType_list_cons [MicaGS HasLC.hasLC Sig]
    (W : TinyML.World) (head tail : Runtime.Val) (t : TinyML.Typ) :
    TinyML.ValHasType W head t ∗ TinyML.ValHasType W tail (.list t) ⊢
      TinyML.ValHasType W (listCons head tail) (.list t) := by
  istart
  iintro H
  icases H with ⟨Hhead, Htail⟩
  iapply (valHasType_list_unfold W (listCons head tail) t).2
  simp only [listCons]
  iapply (TinyML.ValHasType.inj (tag := 1) (arity := 2)
    (s := .tuple [t, .list t]) (ts := [.unit, .tuple [t, .list t]]) (by simp) (by simp))
  iapply (TinyML.ValHasType.tuple W (.tuple [head, tail]) [t, .list t]).2
  iexists [head, tail]
  isplitr
  · ipureintro; rfl
  · iapply (TinyML.ValsHaveTypes.cons W head [tail] t [.list t]).2
    isplitl [Hhead]
    · iexact Hhead
    · iapply (TinyML.ValsHaveTypes.cons W tail [] (.list t) []).2
      isplitl [Htail]
      · iexact Htail
      · exact affine

theorem valHasType_list_cons_raw [MicaGS HasLC.hasLC Sig]
    (W : TinyML.World) (head tail : Runtime.Val) (t : TinyML.Typ) :
    TinyML.ValHasType W head t ∗ TinyML.ValHasType W tail (.list t) ⊢
      TinyML.ValHasType W (.inj 1 2 (.tuple [head, tail])) (.list t) := by
  simpa only [listCons] using valHasType_list_cons W head tail t

theorem valHasType_list_cases [MicaGS HasLC.hasLC Sig]
    (W : TinyML.World) (v : Runtime.Val) (t : TinyML.Typ) :
    TinyML.ValHasType W v (.list t) ⊢
      iprop(⌜v = listNil⌝ ∨ ∃ head tail,
        ⌜v = listCons head tail⌝ ∗
        TinyML.ValHasType W head t ∗ TinyML.ValHasType W tail (.list t)) := by
  istart
  iintro H
  ihave Hsum := (valHasType_list_unfold W v t).1 $$ H
  ihave Hsum := (TinyML.ValHasType.sum W v [.unit, .tuple [t, .list t]]).1 $$ Hsum
  icases Hsum with ⟨%tag, %payload, %hv, Htag⟩
  ihave %hbound := (TinyML.ValSumRel.bound (W := W) (payload := payload)) $$ Htag
  simp at hbound
  have htag : tag = 0 ∨ tag = 1 := by omega
  rcases htag with rfl | rfl
  · ihave Hunit := (TinyML.ValSumRel.zero W payload .unit [.tuple [t, .list t]]).1 $$ Htag
    ihave %hpayload := (TinyML.ValHasType.unit W payload).1 $$ Hunit
    iapply or_intro_l
    ipureintro
    simp [listNil, hv, hpayload]
  · ihave Htuple := (TinyML.ValSumRel.succ W 0 payload .unit [.tuple [t, .list t]]).1 $$ Htag
    ihave Htuple := (TinyML.ValSumRel.zero W payload (.tuple [t, .list t]) []).1 $$ Htuple
    icases (TinyML.ValHasType.tuple W payload [t, .list t]).1 $$ Htuple with
      ⟨%vs, %hpayload, Hvals⟩
    ihave %hlen := TinyML.ValsHaveTypes.length_eq $$ Hvals
    match vs with
    | [head, tail] =>
      iapply or_intro_r
      iexists head, tail
      isplitr
      · ipureintro
        simp [listCons, hv, hpayload]
      · ihave Hvals := (TinyML.ValsHaveTypes.cons W head [tail] t [.list t]).1 $$ Hvals
        icases Hvals with ⟨Hhead, Hvals⟩
        ihave Hvals := (TinyML.ValsHaveTypes.cons W tail [] (.list t) []).1 $$ Hvals
        icases Hvals with ⟨Htail, _⟩
        isplitl [Hhead]
        · iexact Hhead
        · iexact Htail
    | [] | [_] | _ :: _ :: _ :: _ => simp at hlen

/-- Total list length; malformed values have length zero. -/
def listLength : Runtime.Val → Int
  | .inj 1 2 (.tuple [_, tail]) => 1 + listLength tail
  | _ => 0
termination_by value => sizeOf value
decreasing_by simp_wf; omega

/-- Total append; malformed left operands behave like the empty list. -/
def listAppend : Runtime.Val → Runtime.Val → Runtime.Val
  | .inj 1 2 (.tuple [head, tail]), right => listCons head (listAppend tail right)
  | _, right => right
termination_by left _ => sizeOf left
decreasing_by simp_wf; omega

/-- Total reverse on the canonical representation; malformed values are empty. -/
def listRev : Runtime.Val → Runtime.Val
  | .inj 1 2 (.tuple [head, tail]) =>
      listAppend (listRev tail) (listCons head listNil)
  | .inj 0 2 .unit => listNil
  | _ => listNil
termination_by value => sizeOf value
decreasing_by simp_wf; omega

theorem listAppend_typed [MicaGS HasLC.hasLC Sig]
    (W : TinyML.World) (left right : Runtime.Val) (t : TinyML.Typ) :
    TinyML.ValHasType W left (.list t) ∗ TinyML.ValHasType W right (.list t) ⊢
      TinyML.ValHasType W (listAppend left right) (.list t) := by
  istart
  iintro H
  icases H with ⟨Hleft, Hright⟩
  ihave Hcases := valHasType_list_cases W left t $$ Hleft
  icases Hcases with (Hnil | Hcons)
  · ihave %hleft := Hnil
    subst hleft
    simp only [listAppend, listNil]
    iexact Hright
  · icases Hcons with ⟨%head, %tail, %hleft, Hhead, Htail⟩
    subst hleft
    simp only [listCons, listAppend]
    iapply valHasType_list_cons_raw
    isplitl [Hhead]
    · iexact Hhead
    · iapply listAppend_typed
      isplitl [Htail]
      · iexact Htail
      · iexact Hright
termination_by sizeOf left
decreasing_by simp_all [listCons]; omega

theorem listRev_typed [MicaGS HasLC.hasLC Sig]
    (W : TinyML.World) (value : Runtime.Val) (t : TinyML.Typ) :
    TinyML.ValHasType W value (.list t) ⊢
      TinyML.ValHasType W (listRev value) (.list t) := by
  istart
  iintro H
  ihave Hcases := valHasType_list_cases W value t $$ H
  icases Hcases with (Hnil | Hcons)
  · ihave %hvalue := Hnil
    subst hvalue
    simp only [listRev, listNil]
    exact valHasType_list_nil W t
  · icases Hcons with ⟨%head, %tail, %hvalue, Hhead, Htail⟩
    subst hvalue
    simp only [listCons, listRev]
    iapply listAppend_typed
    isplitl [Htail]
    · iapply listRev_typed
      iexact Htail
    · iapply valHasType_list_cons_raw
      isplitl [Hhead]
      · iexact Hhead
      · exact valHasType_list_nil W t
termination_by sizeOf value
decreasing_by simp_all [listCons]; omega

/-! ## Intrinsics -/

private def listTy : TinyML.Typ := .list (.tvar "a")

def listLengthB : Pure.Unary where
  name := "list_length"
  path := some ("List", ["length"])
  arg := .logical listTy
  res := .int
  f := listLength
  dom := fun _ => True
  pre := none
  -- Recursive equations cause unrelated quantified proofs to diverge in Z3;
  -- keep the symbol opaque while retaining its executable, typed semantics.
  defAxiom := .true_

def listLengthIntrinsic : Intrinsic := listLengthB.toIntrinsic

@[simp] theorem listLengthIntrinsic_arity : listLengthIntrinsic.arity = .one := rfl
@[simp] theorem listLengthIntrinsic_folSym : listLengthIntrinsic.folSym = some listLengthB.sym := rfl
@[simp] theorem listLengthSym_name : listLengthB.sym.name = "list_length" := rfl

def listLengthLawful : listLengthB.Lawful where
  argL := Embedding.lawfulLogical listTy
  resL := Embedding.lawfulInt
  domSound := fun _ _ _ => trivial
  semWellTyped := fun _ _ _ _ => affine
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf := by apply Formula.checkWf_ok; rfl
  typeWf := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval := by simp [listLengthB, Formula.eval]

instance : IntrinsicSound [listLengthIntrinsic] listLengthIntrinsic :=
  listLengthLawful.sound

def listAppendB : Pure.Binary where
  name := "list_append"
  path := some ("List", ["append"])
  arg₁ := .logical listTy
  arg₂ := .logical listTy
  res := .logical listTy
  f := listAppend
  dom := fun _ _ => True
  pre := none
  -- See `listLengthB`: recursive list equations are intentionally opaque.
  defAxiom := .true_

def listAppendIntrinsic : Intrinsic := listAppendB.toIntrinsic

@[simp] theorem listAppendIntrinsic_arity : listAppendIntrinsic.arity = .two := rfl
@[simp] theorem listAppendIntrinsic_folSym : listAppendIntrinsic.folSym = some listAppendB.sym := rfl
@[simp] theorem listAppendSym_name : listAppendB.sym.name = "list_append" := rfl

def listAppendLawful : listAppendB.Lawful where
  argL₁ := Embedding.lawfulLogical listTy
  argL₂ := Embedding.lawfulLogical listTy
  resL := Embedding.lawfulLogical listTy
  domSound := fun _ _ _ _ => trivial
  semWellTyped := by
    refine fun σ W (left : Runtime.Val) (right : Runtime.Val) _ => ?_
    simpa [listAppendB, Embedding.logical, listTy, TinyML.Typ.subst] using
      listAppend_typed W left right (σ "a")
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf := by apply Formula.checkWf_ok; rfl
  typeWf := fun _ h => nomatch h
  defEval := by simp [listAppendB, Formula.eval]

instance : IntrinsicSound [listAppendIntrinsic] listAppendIntrinsic :=
  listAppendLawful.sound

def listRevB : Pure.Unary where
  name := "list_rev"
  path := some ("List", ["rev"])
  arg := .logical listTy
  res := .logical listTy
  f := listRev
  dom := fun _ => True
  pre := none
  -- Reverse is deliberately opaque to SMT. Its natural recursive equation
  -- mentions List.append; intrinsic definitions do not carry dependency lists.
  defAxiom := .true_

def listRevIntrinsic : Intrinsic := listRevB.toIntrinsic

@[simp] theorem listRevIntrinsic_arity : listRevIntrinsic.arity = .one := rfl
@[simp] theorem listRevIntrinsic_folSym : listRevIntrinsic.folSym = some listRevB.sym := rfl
@[simp] theorem listRevSym_name : listRevB.sym.name = "list_rev" := rfl

def listRevLawful : listRevB.Lawful where
  argL := Embedding.lawfulLogical listTy
  resL := Embedding.lawfulLogical listTy
  domSound := fun _ _ _ => trivial
  semWellTyped := by
    refine fun σ W (value : Runtime.Val) _ => ?_
    simpa [listRevB, Embedding.logical, listTy, TinyML.Typ.subst] using
      listRev_typed W value (σ "a")
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf := by apply Formula.checkWf_ok; rfl
  typeWf := fun _ h => nomatch h
  defEval := by simp [listRevB, Formula.eval]

instance : IntrinsicSound [listRevIntrinsic] listRevIntrinsic :=
  listRevLawful.sound

end Intrinsics

end Stdlib

-- SUMMARY: Canonical option representation and polymorphic Option intrinsics.
import Mica.Stdlib.Combinators

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

theorem valHasType_option_unfold [MicaGS HasLC.hasLC Sig]
    (W : TinyML.World) (v : Runtime.Val) (t : TinyML.Typ) :
    TinyML.ValHasType W v (.option t) ⊣⊢
      TinyML.ValHasType W v (.sum [.unit, t]) := by
  apply TinyML.ValHasType.named_of_unfold
  simp [TinyML.TypeName.unfold, TinyML.Predef.arity, TinyML.Predef.decl, TinyML.Predef.tparams,
    TinyML.Predef.ctors, TinyML.DataDecl.instantiate, TinyML.Typ.subst]

/-- Runtime representation of the predefined `None` constructor. -/
def optionNone : Runtime.Val := .inj 0 2 .unit

/-- Runtime representation of the predefined `Some` constructor. -/
def optionSome (value : Runtime.Val) : Runtime.Val := .inj 1 2 value

theorem valHasType_option_cases [MicaGS HasLC.hasLC Sig]
    (W : TinyML.World) (v : Runtime.Val) (t : TinyML.Typ) :
    TinyML.ValHasType W v (.option t) ⊢
      iprop(⌜v = optionNone⌝ ∨ ∃ value,
        ⌜v = optionSome value⌝ ∗ TinyML.ValHasType W value t) := by
  istart
  iintro H
  ihave Hsum := (valHasType_option_unfold W v t).1 $$ H
  ihave Hsum := (TinyML.ValHasType.sum W v [.unit, t]).1 $$ Hsum
  icases Hsum with ⟨%tag, %payload, %hv, Htag⟩
  ihave %hbound := (TinyML.ValSumRel.bound (W := W) (payload := payload)) $$ Htag
  simp at hbound
  have htag : tag = 0 ∨ tag = 1 := by omega
  rcases htag with rfl | rfl
  · ihave Hunit := (TinyML.ValSumRel.zero W payload .unit [t]).1 $$ Htag
    ihave %hpayload := (TinyML.ValHasType.unit W payload).1 $$ Hunit
    iapply or_intro_l
    ipureintro
    simp [optionNone, hv, hpayload]
  · ihave Hvalue := (TinyML.ValSumRel.succ W 0 payload .unit [t]).1 $$ Htag
    ihave Hvalue := (TinyML.ValSumRel.zero W payload t []).1 $$ Hvalue
    iapply or_intro_r
    iexists payload
    isplitr
    · ipureintro
      simp [optionSome, hv]
    · iexact Hvalue

/-- Whether a runtime option is a `Some`. -/
def optionIsSome : Runtime.Val → Bool
  | .inj 1 2 _ => true
  | _ => false

/-- Whether a runtime option is `None`. -/
def optionIsNone : Runtime.Val → Bool
  | .inj 0 2 .unit => true
  | _ => false

/-- Extract a `Some` payload; malformed values use the harmless unit fallback. -/
def optionValue : Runtime.Val → Runtime.Val
  | .inj 1 2 value => value
  | _ => .unit

theorem optionValue_typed [MicaGS HasLC.hasLC Sig]
    (W : TinyML.World) (option value : Runtime.Val) (t : TinyML.Typ)
    (hvalue : option = optionSome value) :
    TinyML.ValHasType W option (.option t) ⊢
      TinyML.ValHasType W (optionValue option) t := by
  istart
  iintro H
  ihave Hcases := valHasType_option_cases W option t $$ H
  icases Hcases with (Hnone | Hsome)
  · ihave %hnone := Hnone
    rw [hnone] at hvalue
    simp [optionNone, optionSome] at hvalue
  · icases Hsome with ⟨%payload, %hsome, Hpayload⟩
    have hpayload : payload = value := by
      rw [hsome] at hvalue
      simpa [optionSome] using hvalue
    subst payload
    rw [hvalue]
    simp [optionSome, optionValue]

/-! ## SMT formulas and intrinsics -/

private def optionNoneTerm : Term .value :=
  .unop (.ofInj 0 2) (.const .unit)

private def optionSomeTerm (value : Term .value) : Term .value :=
  .unop (.ofInj 1 2) value

private def optionSomePre (name : String) : Formula :=
  .eq .value (.var .value name)
    (optionSomeTerm (.unop .payloadOf (.var .value name)))

private def optionPayload : Runtime.Val → Runtime.Val
  | .inj _ _ payload => payload
  | _ => .unit

def optionIsSomeDefAxiom : Formula :=
  .and
    (.eq .bool (.unop .toBool (unTerm "option_is_some" optionNoneTerm)) (.const (.b false)))
    (.forall_ "value" .value
      [.term (unTerm "option_is_some" (optionSomeTerm (.var .value "value")))] <|
      .eq .bool
        (.unop .toBool (unTerm "option_is_some" (optionSomeTerm (.var .value "value"))))
        (.const (.b true)))

def optionIsNoneDefAxiom : Formula :=
  .and
    (.eq .bool (.unop .toBool (unTerm "option_is_none" optionNoneTerm)) (.const (.b true)))
    (.forall_ "value" .value
      [.term (unTerm "option_is_none" (optionSomeTerm (.var .value "value")))] <|
      .eq .bool
        (.unop .toBool (unTerm "option_is_none" (optionSomeTerm (.var .value "value"))))
        (.const (.b false)))

def optionValueDefAxiom : Formula :=
  .forall_ "value" .value
    [.term (unTerm "option_value" (optionSomeTerm (.var .value "value")))] <|
    .eq .value
      (unTerm "option_value" (optionSomeTerm (.var .value "value")))
      (.var .value "value")

private def optionTy : TinyML.Typ := .option (.tvar "a")

def optionIsSomeB : Pure.Unary where
  name := "option_is_some"
  path := some ("Option", ["is_some"])
  arg := .logical optionTy
  res := .bool
  f := optionIsSome
  dom := fun _ => True
  pre := none
  defAxiom := optionIsSomeDefAxiom

def optionIsSomeIntrinsic : Intrinsic := optionIsSomeB.toIntrinsic

@[simp] theorem optionIsSomeIntrinsic_arity : optionIsSomeIntrinsic.arity = .one := rfl
@[simp] theorem optionIsSomeIntrinsic_folSym :
    optionIsSomeIntrinsic.folSym = some optionIsSomeB.sym := rfl
@[simp] theorem optionIsSomeSym_name : optionIsSomeB.sym.name = "option_is_some" := rfl

def optionIsSomeLawful : optionIsSomeB.Lawful where
  argL := Embedding.lawfulLogical optionTy
  resL := Embedding.lawfulBool
  domSound := fun _ _ _ => trivial
  semWellTyped := fun _ _ _ _ => affine
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf := by apply Formula.checkWf_ok; rfl
  typeWf := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval := by
    intrinsic_def_eval [unTerm, optionIsSomeB, optionIsSomeDefAxiom,
      optionNoneTerm, optionSomeTerm, optionNone, optionSome, optionIsSome,
      Embedding.logical]

instance : IntrinsicSound [optionIsSomeIntrinsic] optionIsSomeIntrinsic :=
  optionIsSomeLawful.sound

def optionIsNoneB : Pure.Unary where
  name := "option_is_none"
  path := some ("Option", ["is_none"])
  arg := .logical optionTy
  res := .bool
  f := optionIsNone
  dom := fun _ => True
  pre := none
  defAxiom := optionIsNoneDefAxiom

def optionIsNoneIntrinsic : Intrinsic := optionIsNoneB.toIntrinsic

@[simp] theorem optionIsNoneIntrinsic_arity : optionIsNoneIntrinsic.arity = .one := rfl
@[simp] theorem optionIsNoneIntrinsic_folSym :
    optionIsNoneIntrinsic.folSym = some optionIsNoneB.sym := rfl
@[simp] theorem optionIsNoneSym_name : optionIsNoneB.sym.name = "option_is_none" := rfl

def optionIsNoneLawful : optionIsNoneB.Lawful where
  argL := Embedding.lawfulLogical optionTy
  resL := Embedding.lawfulBool
  domSound := fun _ _ _ => trivial
  semWellTyped := fun _ _ _ _ => affine
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf := by apply Formula.checkWf_ok; rfl
  typeWf := by intro φ h; injection h with h; subst h; apply Formula.checkWf_ok; rfl
  defEval := by
    intrinsic_def_eval [unTerm, optionIsNoneB, optionIsNoneDefAxiom,
      optionNoneTerm, optionSomeTerm, optionNone, optionSome, optionIsNone,
      Embedding.logical]

instance : IntrinsicSound [optionIsNoneIntrinsic] optionIsNoneIntrinsic :=
  optionIsNoneLawful.sound

def optionValueB : Pure.Unary where
  name := "option_value"
  path := some ("Option", ["value"])
  arg := .logical optionTy
  res := .poly "a"
  f := optionValue
  dom := fun option => ∃ value, option = optionSome value
  pre := some optionSomePre
  defAxiom := optionValueDefAxiom

def optionValueIntrinsic : Intrinsic := optionValueB.toIntrinsic

@[simp] theorem optionValueIntrinsic_arity : optionValueIntrinsic.arity = .one := rfl
@[simp] theorem optionValueIntrinsic_folSym :
    optionValueIntrinsic.folSym = some optionValueB.sym := rfl
@[simp] theorem optionValueSym_name : optionValueB.sym.name = "option_value" := rfl

def optionValueLawful : optionValueB.Lawful where
  argL := Embedding.lawfulLogical optionTy
  resL := Embedding.lawfulPoly "a"
  domSound := by
    intro ρ option h
    have hpre := h optionSomePre rfl
    refine ⟨optionPayload option, ?_⟩
    simpa [optionValueB, optionSomePre, optionSomeTerm, optionSome,
      optionPayload, Formula.eval, Term.eval,
      Env.lookupConst_updateConst_same] using hpre
  semWellTyped := by
    refine fun σ W (option : Runtime.Val) hdom => ?_
    obtain ⟨value, hvalue⟩ := hdom
    simpa [optionValueB, Embedding.logical, Embedding.poly, optionTy,
      TinyML.Typ.subst] using optionValue_typed W option value (σ "a") hvalue
  specBaseWf := by apply PredTrans.checkWf_ok; rfl
  defWf := by apply Formula.checkWf_ok; rfl
  typeWf := fun _ h => nomatch h
  defEval := by
    intrinsic_def_eval [unTerm, optionValueB, optionValueDefAxiom,
      optionSomeTerm, optionSome, optionValue, Embedding.logical]

instance : IntrinsicSound [optionValueIntrinsic] optionValueIntrinsic :=
  optionValueLawful.sound

end Intrinsics

end Stdlib

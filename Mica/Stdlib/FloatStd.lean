-- SUMMARY: IEEE binary64 float intrinsics (`Float.abs`, `add`, `min`, `equal`, `nan`, …) and soundness instances.
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

/-! ## Trust boundary

Each *primitive* `FloatBits` op (`add`, `sub`, `mul`, `div`, `abs`, `neg`,
`sqrt`, `ofInt`, `eq`, `lt`, `le`, `isNaN`, `isInf`, `isNegative`; defined in
`Mica/FOL/Terms.lean`) is *trusted equal* to the single SMT-LIB `fp.*` op it
prints. Sharing those helpers between `UnOp.eval`/`BinOp.eval` and the symbol
`interp`s below makes each primitive's defining axiom hold by reflexivity.

No NaN canonicalization is performed. This is *not* a source of unsoundness,
because we do not map Float.equal to Z3's builtin equality relation. It is
mapped to fp.eq instead, which properly handles the "NaN equals NaN" case.  -/

/-- Float projection of a runtime value, matching FOL's `toFloat`. -/
private def valFloat : Runtime.Val → UInt64
  | .float b => b
  | _        => 0

/-- Integer projection of a runtime value, matching FOL's `toInt`. -/
private def valInt : Runtime.Val → Int
  | .int n => n
  | _      => 0

/-- Boolean projection of a runtime value, matching FOL's `toBool`. -/
private def valBool : Runtime.Val → Bool
  | .bool b => b
  | _       => false

@[simp] private theorem valFloat_float (b : UInt64) : valFloat (.float b) = b := rfl
@[simp] private theorem valInt_int (n : Int) : valInt (.int n) = n := rfl
@[simp] private theorem valBool_bool (b : Bool) : valBool (.bool b) = b := rfl

@[simp] private theorem toFloat_eq_valFloat (ρ : Env) (v : Runtime.Val) :
    UnOp.eval ρ .toFloat v = valFloat v := rfl
@[simp] private theorem toInt_eq_valInt (ρ : Env) (v : Runtime.Val) :
    UnOp.eval ρ .toInt v = valInt v := rfl
@[simp] private theorem toBool_eq_valBool (ρ : Env) (v : Runtime.Val) :
    UnOp.eval ρ .toBool v = valBool v := rfl

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
@[simp] theorem floatNegInfinitySym_name : floatNegInfinitySym.name = "float_neg_infinity" := rfl

/-! ## Term builders -/

private def unTerm (name : String) (x : Term .value) : Term .value :=
  .unop (.uninterpreted name .value .value) x
private def binTerm (name : String) (x y : Term .value) : Term .value :=
  .binop (.uninterpreted name .value .value .value) x y
private def constTerm (name : String) : Term .value :=
  .const (.uninterpreted name .value)

/-! ## Shared helpers (the StringStd helpers, re-stated locally) -/

private theorem off_shape_zero {Θ : TinyML.TypeEnv} {vs : List Runtime.Val}
    (P : iProp) (hlen : vs.length ≠ 0) :
    TinyML.ValsHaveTypes Θ vs [] ⊢ P := by
  refine TinyML.ValsHaveTypes.length_eq.trans ?_
  iintro %h
  simp only [List.length_nil] at h; omega

private theorem off_shape_one {Θ : TinyML.TypeEnv} {vs : List Runtime.Val} {ty : TinyML.Typ}
    (P : iProp) (hlen : vs.length ≠ 1) :
    TinyML.ValsHaveTypes Θ vs [ty] ⊢ P := by
  refine TinyML.ValsHaveTypes.length_eq.trans ?_
  iintro %h
  simp at h; omega

private theorem off_shape_two_ty {Θ : TinyML.TypeEnv} {vs : List Runtime.Val} {ty₁ ty₂ : TinyML.Typ}
    (P : iProp) (hlen : vs.length ≠ 2) :
    TinyML.ValsHaveTypes Θ vs [ty₁, ty₂] ⊢ P := by
  refine TinyML.ValsHaveTypes.length_eq.trans ?_
  iintro %h
  simp at h; omega

private theorem assert_ret_apply (Θ : TinyML.TypeEnv) (Φ : Runtime.Val → iProp)
    (s : String) (ρ : VerifM.Env) (φ : Formula) (v : Runtime.Val)
    (hφ : φ.eval (ρ.updateConst .value s v).env) :
    PredTrans.apply Θ Φ (.ret (s, .assert φ (.ret ()))) ρ ⊢ Φ v := by
  simp only [PredTrans.apply, Assertion.pre, Assertion.post]
  refine (forall_elim v).trans ?_
  iintro Hw
  iapply Hw
  ipure_intro
  exact hφ

private theorem respects_updateConstE_one {ρ : Env} {s : FOL.Symbol .one}
    {τ : Srt} {x : String} {v : τ.denote} (h : ρ.respects (some s)) :
    (ρ.updateConst τ x v).respects (some s) := by
  show (ρ.updateConst τ x v).unary .value .value s.name = _
  rw [Env.updateConst_unary]; exact h

private theorem respects_updateConstE_two {ρ : Env} {s : FOL.Symbol .two}
    {τ : Srt} {x : String} {v : τ.denote} (h : ρ.respects (some s)) :
    (ρ.updateConst τ x v).respects (some s) := by
  show (ρ.updateConst τ x v).binary .value .value .value s.name = _
  rw [Env.updateConst_binary]; exact h

private theorem respects_argsEnv_one {s : FOL.Symbol .one} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (name, _) :: rest, v :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine respects_argsEnv_one rest vs ?_
      rw [VerifM.Env.updateConst_env]; exact respects_updateConstE_one h

private theorem respects_argsEnv_two {s : FOL.Symbol .two} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (name, _) :: rest, v :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine respects_argsEnv_two rest vs ?_
      rw [VerifM.Env.updateConst_env]; exact respects_updateConstE_two h

/-! ## `Float.abs` (unary `float → float`) -/

def floatAbsDefAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_abs" (.var .value "a"))] <|
    .eq .float (.unop .toFloat (unTerm "float_abs" (.var .value "a")))
      (.unop .fpAbs (.unop .toFloat (.var .value "a")))

def floatAbsTypeAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_abs" (.var .value "a"))] <|
    .unpred .isFloat (unTerm "float_abs" (.var .value "a"))

def floatAbs : Intrinsic where
  arity  := .one
  name   := "float_abs"
  path   := some ("Float", ["abs"])
  reduce := fun a v => ∃ x : UInt64, a = .float x ∧ v = .float (FloatBits.abs x)
  wp     := fun a Q => iprop(∃ x : UInt64, ⌜a = .float x⌝ ∗ Q (.float (FloatBits.abs x)))
  spec   :=
    { args  := [("a", .float)]
      retTy := .float
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") (unTerm "float_abs" (.var .value "a"))) (.ret ())) }
  folSym := some floatAbsSym
  axioms := [floatAbsDefAxiom, floatAbsTypeAxiom]

@[simp] theorem floatAbs_arity : floatAbs.arity = .one := rfl
@[simp] theorem floatAbs_folSym : floatAbs.folSym = some floatAbsSym := rfl
@[simp] theorem floatAbs_toWp (a : Runtime.Val) (Q : Runtime.Val → iProp) :
    floatAbs.toWp [a] Q = iprop(∃ x : UInt64, ⌜a = .float x⌝ ∗ Q (.float (FloatBits.abs x))) :=
  Intrinsic.toWp_one_of_arity _ _ _ _ _ _ _ _ Q

private theorem floatAbs_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [floatAbs]).declVars (Spec.argVars floatAbs.specArgs)) floatAbs.spec.pred := by
  apply PredTrans.checkWf_ok; rfl

private theorem floatAbs_assert_eval (ρ : VerifM.Env) (x : UInt64)
    (hρ : ρ.env.respects (some floatAbsSym)) :
    (Formula.eq .value (.var .value "ret") (unTerm "float_abs" (.var .value "a"))).eval
      ((Spec.argsEnv ρ floatAbs.specArgs [.float x]).updateConst .value "ret" (.float (FloatBits.abs x))).env := by
  have hargs := respects_argsEnv_one floatAbs.specArgs [.float x] hρ
  have hun : (Spec.argsEnv ρ floatAbs.specArgs [.float x]).env.unary
      .value .value "float_abs" = floatAbsSym.interp := by
    simpa [Env.respects, floatAbsSym] using hargs
  show Runtime.Val.float (FloatBits.abs x) =
    (Spec.argsEnv ρ floatAbs.specArgs [.float x]).env.unary .value .value "float_abs" (.float x)
  simp [hun, floatAbsSym]

instance : IntrinsicSound [floatAbs] floatAbs where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [floatAbs, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · have hbase : floatAbsDefAxiom.wfIn (Intrinsic.sigOf [floatAbs]) := by
        simp [floatAbsDefAxiom, unTerm, Intrinsic.sigOf, Intrinsic.foldSig, floatAbs,
          floatAbsSym, Formula.wfIn, Term.wfIn, UnOp.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
    · have hbase : floatAbsTypeAxiom.wfIn (Intrinsic.sigOf [floatAbs]) := by
        simp [floatAbsTypeAxiom, unTerm, Intrinsic.sigOf, Intrinsic.foldSig, floatAbs,
          floatAbsSym, Formula.wfIn, Term.wfIn, UnOp.wfIn, UnPred.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [floatAbs, List.mem_cons, List.not_mem_nil, or_false] at hφ
    have hlen : ρ.respects (some floatAbsSym) := hdeps floatAbs (by simp)
    simp only [Env.respects] at hlen
    have hu : ∀ a : Runtime.Val,
        (ρ.updateConst .value "a" a).unary .value .value "float_abs" = floatAbsSym.interp := by
      intro a; rw [Env.updateConst_unary]; simpa [floatAbsSym] using hlen
    rcases hφ with rfl | rfl
    · simp only [floatAbsDefAxiom, Formula.eval]
      intro a
      simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hu a, floatAbsSym]
      rfl
    · simp only [floatAbsTypeAxiom, Formula.eval]
      intro a
      simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hu a, floatAbsSym]
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono floatAbs_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars floatAbs.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [floatAbs_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.float] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | _ :: _ :: _ => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | [v] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, _⟩
      ihave Hveq := (TinyML.ValHasType.float Θ v).1 $$ Hv
      ipure Hveq
      obtain ⟨x, rfl⟩ := Hveq
      rw [floatAbs_toWp]
      iexists x
      isplitr [Hpred]
      · ipure_intro; rfl
      · refine (assert_ret_apply Θ _ "ret" _ _ (.float (FloatBits.abs x)) ?_).trans ?_
        · exact floatAbs_assert_eval ρ x hρ
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.float_intro Θ (FloatBits.abs x)

/-! ## `Float.neg` (unary `float → float`) -/

def floatNegDefAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_neg" (.var .value "a"))] <|
    .eq .float (.unop .toFloat (unTerm "float_neg" (.var .value "a")))
      (.unop .fpNeg (.unop .toFloat (.var .value "a")))
def floatNegTypeAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_neg" (.var .value "a"))] <|
    .unpred .isFloat (unTerm "float_neg" (.var .value "a"))

def floatNeg : Intrinsic where
  arity  := .one
  name   := "float_neg"
  path   := some ("Float", ["neg"])
  reduce := fun a v => ∃ x : UInt64, a = .float x ∧ v = .float (FloatBits.neg x)
  wp     := fun a Q => iprop(∃ x : UInt64, ⌜a = .float x⌝ ∗ Q (.float (FloatBits.neg x)))
  spec   :=
    { args  := [("a", .float)]
      retTy := .float
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") (unTerm "float_neg" (.var .value "a"))) (.ret ())) }
  folSym := some floatNegSym
  axioms := [floatNegDefAxiom, floatNegTypeAxiom]

@[simp] theorem floatNeg_arity : floatNeg.arity = .one := rfl
@[simp] theorem floatNeg_folSym : floatNeg.folSym = some floatNegSym := rfl
@[simp] theorem floatNeg_toWp (a : Runtime.Val) (Q : Runtime.Val → iProp) :
    floatNeg.toWp [a] Q = iprop(∃ x : UInt64, ⌜a = .float x⌝ ∗ Q (.float (FloatBits.neg x))) :=
  Intrinsic.toWp_one_of_arity _ _ _ _ _ _ _ _ Q

private theorem floatNeg_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [floatNeg]).declVars (Spec.argVars floatNeg.specArgs)) floatNeg.spec.pred := by
  apply PredTrans.checkWf_ok; rfl

private theorem floatNeg_assert_eval (ρ : VerifM.Env) (x : UInt64)
    (hρ : ρ.env.respects (some floatNegSym)) :
    (Formula.eq .value (.var .value "ret") (unTerm "float_neg" (.var .value "a"))).eval
      ((Spec.argsEnv ρ floatNeg.specArgs [.float x]).updateConst .value "ret" (.float (FloatBits.neg x))).env := by
  have hargs := respects_argsEnv_one floatNeg.specArgs [.float x] hρ
  have hun : (Spec.argsEnv ρ floatNeg.specArgs [.float x]).env.unary
      .value .value "float_neg" = floatNegSym.interp := by
    simpa [Env.respects, floatNegSym] using hargs
  show Runtime.Val.float (FloatBits.neg x) =
    (Spec.argsEnv ρ floatNeg.specArgs [.float x]).env.unary .value .value "float_neg" (.float x)
  simp [hun, floatNegSym]

instance : IntrinsicSound [floatNeg] floatNeg where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [floatNeg, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · have hbase : floatNegDefAxiom.wfIn (Intrinsic.sigOf [floatNeg]) := by
        simp [floatNegDefAxiom, unTerm, Intrinsic.sigOf, Intrinsic.foldSig, floatNeg,
          floatNegSym, Formula.wfIn, Term.wfIn, UnOp.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
    · have hbase : floatNegTypeAxiom.wfIn (Intrinsic.sigOf [floatNeg]) := by
        simp [floatNegTypeAxiom, unTerm, Intrinsic.sigOf, Intrinsic.foldSig, floatNeg,
          floatNegSym, Formula.wfIn, Term.wfIn, UnOp.wfIn, UnPred.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [floatNeg, List.mem_cons, List.not_mem_nil, or_false] at hφ
    have hlen : ρ.respects (some floatNegSym) := hdeps floatNeg (by simp)
    simp only [Env.respects] at hlen
    have hu : ∀ a : Runtime.Val,
        (ρ.updateConst .value "a" a).unary .value .value "float_neg" = floatNegSym.interp := by
      intro a; rw [Env.updateConst_unary]; simpa [floatNegSym] using hlen
    rcases hφ with rfl | rfl
    · simp only [floatNegDefAxiom, Formula.eval]
      intro a
      simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hu a, floatNegSym]
      rfl
    · simp only [floatNegTypeAxiom, Formula.eval]
      intro a
      simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hu a, floatNegSym]
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono floatNeg_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars floatNeg.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [floatNeg_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.float] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | _ :: _ :: _ => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | [v] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, _⟩
      ihave Hveq := (TinyML.ValHasType.float Θ v).1 $$ Hv
      ipure Hveq
      obtain ⟨x, rfl⟩ := Hveq
      rw [floatNeg_toWp]
      iexists x
      isplitr [Hpred]
      · ipure_intro; rfl
      · refine (assert_ret_apply Θ _ "ret" _ _ (.float (FloatBits.neg x)) ?_).trans ?_
        · exact floatNeg_assert_eval ρ x hρ
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.float_intro Θ (FloatBits.neg x)

/-! ## `Float.sqrt` (unary `float → float`) -/

def floatSqrtDefAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_sqrt" (.var .value "a"))] <|
    .eq .float (.unop .toFloat (unTerm "float_sqrt" (.var .value "a")))
      (.unop .fpSqrt (.unop .toFloat (.var .value "a")))
def floatSqrtTypeAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_sqrt" (.var .value "a"))] <|
    .unpred .isFloat (unTerm "float_sqrt" (.var .value "a"))

def floatSqrt : Intrinsic where
  arity  := .one
  name   := "float_sqrt"
  path   := some ("Float", ["sqrt"])
  reduce := fun a v => ∃ x : UInt64, a = .float x ∧ v = .float (FloatBits.sqrt x)
  wp     := fun a Q => iprop(∃ x : UInt64, ⌜a = .float x⌝ ∗ Q (.float (FloatBits.sqrt x)))
  spec   :=
    { args  := [("a", .float)]
      retTy := .float
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") (unTerm "float_sqrt" (.var .value "a"))) (.ret ())) }
  folSym := some floatSqrtSym
  axioms := [floatSqrtDefAxiom, floatSqrtTypeAxiom]

@[simp] theorem floatSqrt_arity : floatSqrt.arity = .one := rfl
@[simp] theorem floatSqrt_folSym : floatSqrt.folSym = some floatSqrtSym := rfl
@[simp] theorem floatSqrt_toWp (a : Runtime.Val) (Q : Runtime.Val → iProp) :
    floatSqrt.toWp [a] Q = iprop(∃ x : UInt64, ⌜a = .float x⌝ ∗ Q (.float (FloatBits.sqrt x))) :=
  Intrinsic.toWp_one_of_arity _ _ _ _ _ _ _ _ Q

private theorem floatSqrt_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [floatSqrt]).declVars (Spec.argVars floatSqrt.specArgs)) floatSqrt.spec.pred := by
  apply PredTrans.checkWf_ok; rfl

private theorem floatSqrt_assert_eval (ρ : VerifM.Env) (x : UInt64)
    (hρ : ρ.env.respects (some floatSqrtSym)) :
    (Formula.eq .value (.var .value "ret") (unTerm "float_sqrt" (.var .value "a"))).eval
      ((Spec.argsEnv ρ floatSqrt.specArgs [.float x]).updateConst .value "ret" (.float (FloatBits.sqrt x))).env := by
  have hargs := respects_argsEnv_one floatSqrt.specArgs [.float x] hρ
  have hun : (Spec.argsEnv ρ floatSqrt.specArgs [.float x]).env.unary
      .value .value "float_sqrt" = floatSqrtSym.interp := by
    simpa [Env.respects, floatSqrtSym] using hargs
  show Runtime.Val.float (FloatBits.sqrt x) =
    (Spec.argsEnv ρ floatSqrt.specArgs [.float x]).env.unary .value .value "float_sqrt" (.float x)
  simp [hun, floatSqrtSym]

instance : IntrinsicSound [floatSqrt] floatSqrt where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [floatSqrt, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · have hbase : floatSqrtDefAxiom.wfIn (Intrinsic.sigOf [floatSqrt]) := by
        simp [floatSqrtDefAxiom, unTerm, Intrinsic.sigOf, Intrinsic.foldSig, floatSqrt,
          floatSqrtSym, Formula.wfIn, Term.wfIn, UnOp.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
    · have hbase : floatSqrtTypeAxiom.wfIn (Intrinsic.sigOf [floatSqrt]) := by
        simp [floatSqrtTypeAxiom, unTerm, Intrinsic.sigOf, Intrinsic.foldSig, floatSqrt,
          floatSqrtSym, Formula.wfIn, Term.wfIn, UnOp.wfIn, UnPred.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [floatSqrt, List.mem_cons, List.not_mem_nil, or_false] at hφ
    have hlen : ρ.respects (some floatSqrtSym) := hdeps floatSqrt (by simp)
    simp only [Env.respects] at hlen
    have hu : ∀ a : Runtime.Val,
        (ρ.updateConst .value "a" a).unary .value .value "float_sqrt" = floatSqrtSym.interp := by
      intro a; rw [Env.updateConst_unary]; simpa [floatSqrtSym] using hlen
    rcases hφ with rfl | rfl
    · simp only [floatSqrtDefAxiom, Formula.eval]
      intro a
      simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hu a, floatSqrtSym]
      rfl
    · simp only [floatSqrtTypeAxiom, Formula.eval]
      intro a
      simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hu a, floatSqrtSym]
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono floatSqrt_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars floatSqrt.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [floatSqrt_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.float] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | _ :: _ :: _ => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | [v] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, _⟩
      ihave Hveq := (TinyML.ValHasType.float Θ v).1 $$ Hv
      ipure Hveq
      obtain ⟨x, rfl⟩ := Hveq
      rw [floatSqrt_toWp]
      iexists x
      isplitr [Hpred]
      · ipure_intro; rfl
      · refine (assert_ret_apply Θ _ "ret" _ _ (.float (FloatBits.sqrt x)) ?_).trans ?_
        · exact floatSqrt_assert_eval ρ x hρ
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.float_intro Θ (FloatBits.sqrt x)

/-! ## `Float.is_nan` (unary `float → bool`) -/

def floatIsNanDefAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_is_nan" (.var .value "a"))] <|
    .eq .bool (.unop .toBool (unTerm "float_is_nan" (.var .value "a")))
      (.unop .fpIsNaN (.unop .toFloat (.var .value "a")))
def floatIsNanTypeAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_is_nan" (.var .value "a"))] <|
    .unpred .isBool (unTerm "float_is_nan" (.var .value "a"))

def floatIsNan : Intrinsic where
  arity  := .one
  name   := "float_is_nan"
  path   := some ("Float", ["is_nan"])
  reduce := fun a v => ∃ x : UInt64, a = .float x ∧ v = .bool (FloatBits.isNaN x)
  wp     := fun a Q => iprop(∃ x : UInt64, ⌜a = .float x⌝ ∗ Q (.bool (FloatBits.isNaN x)))
  spec   :=
    { args  := [("a", .float)]
      retTy := .bool
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") (unTerm "float_is_nan" (.var .value "a"))) (.ret ())) }
  folSym := some floatIsNanSym
  axioms := [floatIsNanDefAxiom, floatIsNanTypeAxiom]

@[simp] theorem floatIsNan_arity : floatIsNan.arity = .one := rfl
@[simp] theorem floatIsNan_folSym : floatIsNan.folSym = some floatIsNanSym := rfl
@[simp] theorem floatIsNan_toWp (a : Runtime.Val) (Q : Runtime.Val → iProp) :
    floatIsNan.toWp [a] Q = iprop(∃ x : UInt64, ⌜a = .float x⌝ ∗ Q (.bool (FloatBits.isNaN x))) :=
  Intrinsic.toWp_one_of_arity _ _ _ _ _ _ _ _ Q

private theorem floatIsNan_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [floatIsNan]).declVars (Spec.argVars floatIsNan.specArgs)) floatIsNan.spec.pred := by
  apply PredTrans.checkWf_ok; rfl

private theorem floatIsNan_assert_eval (ρ : VerifM.Env) (x : UInt64)
    (hρ : ρ.env.respects (some floatIsNanSym)) :
    (Formula.eq .value (.var .value "ret") (unTerm "float_is_nan" (.var .value "a"))).eval
      ((Spec.argsEnv ρ floatIsNan.specArgs [.float x]).updateConst .value "ret" (.bool (FloatBits.isNaN x))).env := by
  have hargs := respects_argsEnv_one floatIsNan.specArgs [.float x] hρ
  have hun : (Spec.argsEnv ρ floatIsNan.specArgs [.float x]).env.unary
      .value .value "float_is_nan" = floatIsNanSym.interp := by
    simpa [Env.respects, floatIsNanSym] using hargs
  show Runtime.Val.bool (FloatBits.isNaN x) =
    (Spec.argsEnv ρ floatIsNan.specArgs [.float x]).env.unary .value .value "float_is_nan" (.float x)
  simp [hun, floatIsNanSym]

instance : IntrinsicSound [floatIsNan] floatIsNan where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [floatIsNan, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · have hbase : floatIsNanDefAxiom.wfIn (Intrinsic.sigOf [floatIsNan]) := by
        simp [floatIsNanDefAxiom, unTerm, Intrinsic.sigOf, Intrinsic.foldSig, floatIsNan,
          floatIsNanSym, Formula.wfIn, Term.wfIn, UnOp.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
    · have hbase : floatIsNanTypeAxiom.wfIn (Intrinsic.sigOf [floatIsNan]) := by
        simp [floatIsNanTypeAxiom, unTerm, Intrinsic.sigOf, Intrinsic.foldSig, floatIsNan,
          floatIsNanSym, Formula.wfIn, Term.wfIn, UnOp.wfIn, UnPred.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [floatIsNan, List.mem_cons, List.not_mem_nil, or_false] at hφ
    have hlen : ρ.respects (some floatIsNanSym) := hdeps floatIsNan (by simp)
    simp only [Env.respects] at hlen
    have hu : ∀ a : Runtime.Val,
        (ρ.updateConst .value "a" a).unary .value .value "float_is_nan" = floatIsNanSym.interp := by
      intro a; rw [Env.updateConst_unary]; simpa [floatIsNanSym] using hlen
    rcases hφ with rfl | rfl
    · simp only [floatIsNanDefAxiom, Formula.eval]
      intro a
      simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hu a, floatIsNanSym]
      rfl
    · simp only [floatIsNanTypeAxiom, Formula.eval]
      intro a
      simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hu a, floatIsNanSym]
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono floatIsNan_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars floatIsNan.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [floatIsNan_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.float] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | _ :: _ :: _ => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | [v] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, _⟩
      ihave Hveq := (TinyML.ValHasType.float Θ v).1 $$ Hv
      ipure Hveq
      obtain ⟨x, rfl⟩ := Hveq
      rw [floatIsNan_toWp]
      iexists x
      isplitr [Hpred]
      · ipure_intro; rfl
      · refine (assert_ret_apply Θ _ "ret" _ _ (.bool (FloatBits.isNaN x)) ?_).trans ?_
        · exact floatIsNan_assert_eval ρ x hρ
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.bool_intro Θ (FloatBits.isNaN x)

/-! ## `Float.is_finite` (unary `float → bool`) -/

/-- `is_finite a` decodes to `¬infinite ∧ ¬nan`, expressed via the Z3 primitives
`fp.isInfinite`/`fp.isNaN` (no Z3 macro). Mirrors `FloatBits.isFinite`. -/
def floatIsFiniteDefAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_is_finite" (.var .value "a"))] <|
    .eq .bool (.unop .toBool (unTerm "float_is_finite" (.var .value "a")))
      (.ite (.unop .fpIsInfinite (.unop .toFloat (.var .value "a"))) (.const (.b false))
        (.ite (.unop .fpIsNaN (.unop .toFloat (.var .value "a"))) (.const (.b false))
          (.const (.b true))))
def floatIsFiniteTypeAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_is_finite" (.var .value "a"))] <|
    .unpred .isBool (unTerm "float_is_finite" (.var .value "a"))

def floatIsFinite : Intrinsic where
  arity  := .one
  name   := "float_is_finite"
  path   := some ("Float", ["is_finite"])
  reduce := fun a v => ∃ x : UInt64, a = .float x ∧ v = .bool (FloatBits.isFinite x)
  wp     := fun a Q => iprop(∃ x : UInt64, ⌜a = .float x⌝ ∗ Q (.bool (FloatBits.isFinite x)))
  spec   :=
    { args  := [("a", .float)]
      retTy := .bool
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") (unTerm "float_is_finite" (.var .value "a"))) (.ret ())) }
  folSym := some floatIsFiniteSym
  axioms := [floatIsFiniteDefAxiom, floatIsFiniteTypeAxiom]

@[simp] theorem floatIsFinite_arity : floatIsFinite.arity = .one := rfl
@[simp] theorem floatIsFinite_folSym : floatIsFinite.folSym = some floatIsFiniteSym := rfl
@[simp] theorem floatIsFinite_toWp (a : Runtime.Val) (Q : Runtime.Val → iProp) :
    floatIsFinite.toWp [a] Q = iprop(∃ x : UInt64, ⌜a = .float x⌝ ∗ Q (.bool (FloatBits.isFinite x))) :=
  Intrinsic.toWp_one_of_arity _ _ _ _ _ _ _ _ Q

private theorem floatIsFinite_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [floatIsFinite]).declVars (Spec.argVars floatIsFinite.specArgs)) floatIsFinite.spec.pred := by
  apply PredTrans.checkWf_ok; rfl

private theorem floatIsFinite_assert_eval (ρ : VerifM.Env) (x : UInt64)
    (hρ : ρ.env.respects (some floatIsFiniteSym)) :
    (Formula.eq .value (.var .value "ret") (unTerm "float_is_finite" (.var .value "a"))).eval
      ((Spec.argsEnv ρ floatIsFinite.specArgs [.float x]).updateConst .value "ret" (.bool (FloatBits.isFinite x))).env := by
  have hargs := respects_argsEnv_one floatIsFinite.specArgs [.float x] hρ
  have hun : (Spec.argsEnv ρ floatIsFinite.specArgs [.float x]).env.unary
      .value .value "float_is_finite" = floatIsFiniteSym.interp := by
    simpa [Env.respects, floatIsFiniteSym] using hargs
  show Runtime.Val.bool (FloatBits.isFinite x) =
    (Spec.argsEnv ρ floatIsFinite.specArgs [.float x]).env.unary .value .value "float_is_finite" (.float x)
  simp [hun, floatIsFiniteSym]

instance : IntrinsicSound [floatIsFinite] floatIsFinite where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [floatIsFinite, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · have hbase : floatIsFiniteDefAxiom.wfIn (Intrinsic.sigOf [floatIsFinite]) := by
        simp [floatIsFiniteDefAxiom, unTerm, Intrinsic.sigOf, Intrinsic.foldSig, floatIsFinite,
          floatIsFiniteSym, Formula.wfIn, Term.wfIn, UnOp.wfIn, Const.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
    · have hbase : floatIsFiniteTypeAxiom.wfIn (Intrinsic.sigOf [floatIsFinite]) := by
        simp [floatIsFiniteTypeAxiom, unTerm, Intrinsic.sigOf, Intrinsic.foldSig, floatIsFinite,
          floatIsFiniteSym, Formula.wfIn, Term.wfIn, UnOp.wfIn, UnPred.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [floatIsFinite, List.mem_cons, List.not_mem_nil, or_false] at hφ
    have hlen : ρ.respects (some floatIsFiniteSym) := hdeps floatIsFinite (by simp)
    simp only [Env.respects] at hlen
    have hu : ∀ a : Runtime.Val,
        (ρ.updateConst .value "a" a).unary .value .value "float_is_finite" = floatIsFiniteSym.interp := by
      intro a; rw [Env.updateConst_unary]; simpa [floatIsFiniteSym] using hlen
    rcases hφ with rfl | rfl
    · simp only [floatIsFiniteDefAxiom, Formula.eval]
      intro a
      simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hu a, floatIsFiniteSym,
        FloatBits.isFinite]
      rfl
    · simp only [floatIsFiniteTypeAxiom, Formula.eval]
      intro a
      simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hu a, floatIsFiniteSym]
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono floatIsFinite_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars floatIsFinite.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [floatIsFinite_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.float] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | _ :: _ :: _ => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | [v] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, _⟩
      ihave Hveq := (TinyML.ValHasType.float Θ v).1 $$ Hv
      ipure Hveq
      obtain ⟨x, rfl⟩ := Hveq
      rw [floatIsFinite_toWp]
      iexists x
      isplitr [Hpred]
      · ipure_intro; rfl
      · refine (assert_ret_apply Θ _ "ret" _ _ (.bool (FloatBits.isFinite x)) ?_).trans ?_
        · exact floatIsFinite_assert_eval ρ x hρ
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.bool_intro Θ (FloatBits.isFinite x)

/-! ## `Float.of_int` (unary `int → float`) -/

def floatOfIntDefAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_of_int" (.var .value "a"))] <|
    .eq .float (.unop .toFloat (unTerm "float_of_int" (.var .value "a")))
      (.unop .fpOfInt (.unop .toInt (.var .value "a")))
def floatOfIntTypeAxiom : Formula :=
  .forall_ "a" .value [.term (unTerm "float_of_int" (.var .value "a"))] <|
    .unpred .isFloat (unTerm "float_of_int" (.var .value "a"))

def floatOfInt : Intrinsic where
  arity  := .one
  name   := "float_of_int"
  path   := some ("Float", ["of_int"])
  reduce := fun a v => ∃ x : Int, a = .int x ∧ v = .float (FloatBits.ofInt x)
  wp     := fun a Q => iprop(∃ x : Int, ⌜a = .int x⌝ ∗ Q (.float (FloatBits.ofInt x)))
  spec   :=
    { args  := [("a", .int)]
      retTy := .float
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") (unTerm "float_of_int" (.var .value "a"))) (.ret ())) }
  folSym := some floatOfIntSym
  axioms := [floatOfIntDefAxiom, floatOfIntTypeAxiom]

@[simp] theorem floatOfInt_arity : floatOfInt.arity = .one := rfl
@[simp] theorem floatOfInt_folSym : floatOfInt.folSym = some floatOfIntSym := rfl
@[simp] theorem floatOfInt_toWp (a : Runtime.Val) (Q : Runtime.Val → iProp) :
    floatOfInt.toWp [a] Q = iprop(∃ x : Int, ⌜a = .int x⌝ ∗ Q (.float (FloatBits.ofInt x))) :=
  Intrinsic.toWp_one_of_arity _ _ _ _ _ _ _ _ Q

private theorem floatOfInt_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [floatOfInt]).declVars (Spec.argVars floatOfInt.specArgs)) floatOfInt.spec.pred := by
  apply PredTrans.checkWf_ok; rfl

private theorem floatOfInt_assert_eval (ρ : VerifM.Env) (x : Int)
    (hρ : ρ.env.respects (some floatOfIntSym)) :
    (Formula.eq .value (.var .value "ret") (unTerm "float_of_int" (.var .value "a"))).eval
      ((Spec.argsEnv ρ floatOfInt.specArgs [.int x]).updateConst .value "ret" (.float (FloatBits.ofInt x))).env := by
  have hargs := respects_argsEnv_one floatOfInt.specArgs [.int x] hρ
  have hun : (Spec.argsEnv ρ floatOfInt.specArgs [.int x]).env.unary
      .value .value "float_of_int" = floatOfIntSym.interp := by
    simpa [Env.respects, floatOfIntSym] using hargs
  show Runtime.Val.float (FloatBits.ofInt x) =
    (Spec.argsEnv ρ floatOfInt.specArgs [.int x]).env.unary .value .value "float_of_int" (.int x)
  simp [hun, floatOfIntSym]

instance : IntrinsicSound [floatOfInt] floatOfInt where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [floatOfInt, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · have hbase : floatOfIntDefAxiom.wfIn (Intrinsic.sigOf [floatOfInt]) := by
        simp [floatOfIntDefAxiom, unTerm, Intrinsic.sigOf, Intrinsic.foldSig, floatOfInt,
          floatOfIntSym, Formula.wfIn, Term.wfIn, UnOp.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
    · have hbase : floatOfIntTypeAxiom.wfIn (Intrinsic.sigOf [floatOfInt]) := by
        simp [floatOfIntTypeAxiom, unTerm, Intrinsic.sigOf, Intrinsic.foldSig, floatOfInt,
          floatOfIntSym, Formula.wfIn, Term.wfIn, UnOp.wfIn, UnPred.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [floatOfInt, List.mem_cons, List.not_mem_nil, or_false] at hφ
    have hlen : ρ.respects (some floatOfIntSym) := hdeps floatOfInt (by simp)
    simp only [Env.respects] at hlen
    have hu : ∀ a : Runtime.Val,
        (ρ.updateConst .value "a" a).unary .value .value "float_of_int" = floatOfIntSym.interp := by
      intro a; rw [Env.updateConst_unary]; simpa [floatOfIntSym] using hlen
    rcases hφ with rfl | rfl
    · simp only [floatOfIntDefAxiom, Formula.eval]
      intro a
      simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hu a, floatOfIntSym]
      rfl
    · simp only [floatOfIntTypeAxiom, Formula.eval]
      intro a
      simp [unTerm, Term.eval, Env.lookupConst_updateConst_same, hu a, floatOfIntSym]
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono floatOfInt_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars floatOfInt.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [floatOfInt_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.int] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | _ :: _ :: _ => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | [v] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, _⟩
      ihave Hveq := (TinyML.ValHasType.int Θ v).1 $$ Hv
      ipure Hveq
      obtain ⟨x, rfl⟩ := Hveq
      rw [floatOfInt_toWp]
      iexists x
      isplitr [Hpred]
      · ipure_intro; rfl
      · refine (assert_ret_apply Θ _ "ret" _ _ (.float (FloatBits.ofInt x)) ?_).trans ?_
        · exact floatOfInt_assert_eval ρ x hρ
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.float_intro Θ (FloatBits.ofInt x)

/-! ## Binary `float → float → float` intrinsics -/

private def binFloatDefAxiom (sym : FOL.Symbol .two) (op : BinOp .float .float .float) : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm sym.name (.var .value "a") (.var .value "b"))] <|
    .eq .float (.unop .toFloat (binTerm sym.name (.var .value "a") (.var .value "b")))
      (.binop op (.unop .toFloat (.var .value "a")) (.unop .toFloat (.var .value "b")))

private def binFloatTypeAxiom (sym : FOL.Symbol .two) : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm sym.name (.var .value "a") (.var .value "b"))] <|
    .unpred .isFloat (binTerm sym.name (.var .value "a") (.var .value "b"))

private def mkBinFloat (sym : FOL.Symbol .two) (pathTail : String)
    (bits : UInt64 → UInt64 → UInt64) (op : BinOp .float .float .float) : Intrinsic where
  arity  := .two
  name   := sym.name
  path   := some ("Float", [pathTail])
  reduce := fun (a, b) v => ∃ x y : UInt64, a = .float x ∧ b = .float y ∧ v = .float (bits x y)
  wp     := fun (a, b) Q => iprop(∃ x y : UInt64, ⌜a = .float x ∧ b = .float y⌝ ∗ Q (.float (bits x y)))
  spec   :=
    { args  := [("a", .float), ("b", .float)]
      retTy := .float
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") (binTerm sym.name (.var .value "a") (.var .value "b"))) (.ret ())) }
  folSym := some sym
  axioms := [binFloatDefAxiom sym op, binFloatTypeAxiom sym]

@[simp] theorem mkBinFloat_arity (sym : FOL.Symbol .two) (pathTail bits op) :
    (mkBinFloat sym pathTail bits op).arity = .two := rfl
@[simp] theorem mkBinFloat_folSym (sym : FOL.Symbol .two) (pathTail bits op) :
    (mkBinFloat sym pathTail bits op).folSym = some sym := rfl
@[simp] theorem mkBinFloat_toWp (sym : FOL.Symbol .two) (pathTail bits op)
    (a b : Runtime.Val) (Q : Runtime.Val → iProp) :
    (mkBinFloat sym pathTail bits op).toWp [a, b] Q =
      iprop(∃ x y : UInt64, ⌜a = .float x ∧ b = .float y⌝ ∗ Q (.float (bits x y))) :=
  Intrinsic.toWp_two_of_arity _ _ _ _ _ _ _ _ _ Q

/-- Like `mkBinFloat`, but with a caller-supplied definitional axiom instead of a
single `op` head. Used by `min`/`max`, whose OCaml semantics are an `ite` cascade
over `fp.isNaN`/`fp.lt`/`fp.isNegative` rather than one SMT-LIB primitive. -/
private def mkBinFloatWith (sym : FOL.Symbol .two) (pathTail : String)
    (bits : UInt64 → UInt64 → UInt64) (defAxiom : Formula) : Intrinsic where
  arity  := .two
  name   := sym.name
  path   := some ("Float", [pathTail])
  reduce := fun (a, b) v => ∃ x y : UInt64, a = .float x ∧ b = .float y ∧ v = .float (bits x y)
  wp     := fun (a, b) Q => iprop(∃ x y : UInt64, ⌜a = .float x ∧ b = .float y⌝ ∗ Q (.float (bits x y)))
  spec   :=
    { args  := [("a", .float), ("b", .float)]
      retTy := .float
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") (binTerm sym.name (.var .value "a") (.var .value "b"))) (.ret ())) }
  folSym := some sym
  axioms := [defAxiom, binFloatTypeAxiom sym]

@[simp] theorem mkBinFloatWith_arity (sym : FOL.Symbol .two) (pathTail bits defAxiom) :
    (mkBinFloatWith sym pathTail bits defAxiom).arity = .two := rfl
@[simp] theorem mkBinFloatWith_folSym (sym : FOL.Symbol .two) (pathTail bits defAxiom) :
    (mkBinFloatWith sym pathTail bits defAxiom).folSym = some sym := rfl
@[simp] theorem mkBinFloatWith_toWp (sym : FOL.Symbol .two) (pathTail bits defAxiom)
    (a b : Runtime.Val) (Q : Runtime.Val → iProp) :
    (mkBinFloatWith sym pathTail bits defAxiom).toWp [a, b] Q =
      iprop(∃ x y : UInt64, ⌜a = .float x ∧ b = .float y⌝ ∗ Q (.float (bits x y))) :=
  Intrinsic.toWp_two_of_arity _ _ _ _ _ _ _ _ _ Q

/-- `Float.min`, OCaml-faithful incl. signed zero (see `FloatBits.min`). The
definitional axiom is an `ite` cascade over the Z3 primitives, mirroring the
`bif`-structure of `FloatBits.min` so the soundness proof is reflexive. -/
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

/-- `Float.max`, OCaml-faithful incl. signed zero (see `FloatBits.max`). -/
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

def floatAdd : Intrinsic := mkBinFloat floatAddSym "add" FloatBits.add .fpAdd
def floatSub : Intrinsic := mkBinFloat floatSubSym "sub" FloatBits.sub .fpSub
def floatMul : Intrinsic := mkBinFloat floatMulSym "mul" FloatBits.mul .fpMul
def floatDiv : Intrinsic := mkBinFloat floatDivSym "div" FloatBits.div .fpDiv
def floatMin : Intrinsic := mkBinFloatWith floatMinSym "min" FloatBits.min floatMinDefAxiom
def floatMax : Intrinsic := mkBinFloatWith floatMaxSym "max" FloatBits.max floatMaxDefAxiom

@[simp] theorem floatAdd_arity : floatAdd.arity = .two := rfl
@[simp] theorem floatSub_arity : floatSub.arity = .two := rfl
@[simp] theorem floatMul_arity : floatMul.arity = .two := rfl
@[simp] theorem floatDiv_arity : floatDiv.arity = .two := rfl
@[simp] theorem floatMin_arity : floatMin.arity = .two := rfl
@[simp] theorem floatMax_arity : floatMax.arity = .two := rfl
@[simp] theorem floatAdd_folSym : floatAdd.folSym = some floatAddSym := rfl
@[simp] theorem floatSub_folSym : floatSub.folSym = some floatSubSym := rfl
@[simp] theorem floatMul_folSym : floatMul.folSym = some floatMulSym := rfl
@[simp] theorem floatDiv_folSym : floatDiv.folSym = some floatDivSym := rfl
@[simp] theorem floatMin_folSym : floatMin.folSym = some floatMinSym := rfl
@[simp] theorem floatMax_folSym : floatMax.folSym = some floatMaxSym := rfl

private theorem floatAdd_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [floatAdd]).declVars (Spec.argVars floatAdd.specArgs)) floatAdd.spec.pred := by
  apply PredTrans.checkWf_ok; rfl

private theorem floatAdd_assert_eval (ρ : VerifM.Env) (x y : UInt64)
    (hρ : ρ.env.respects (some floatAddSym)) :
    (Formula.eq .value (.var .value "ret") (binTerm "float_add" (.var .value "a") (.var .value "b"))).eval
      ((Spec.argsEnv ρ floatAdd.specArgs [.float x, .float y]).updateConst
        .value "ret" (.float (FloatBits.add x y))).env := by
  have hargs := respects_argsEnv_two floatAdd.specArgs [.float x, .float y] hρ
  have hbin : (Spec.argsEnv ρ floatAdd.specArgs [.float x, .float y]).env.binary
      .value .value .value "float_add" = fun a b => floatAddSym.interp (a, b) := by
    simpa [Env.respects, floatAddSym] using hargs
  show Runtime.Val.float (FloatBits.add x y) =
    (Spec.argsEnv ρ floatAdd.specArgs [.float x, .float y]).env.binary
      .value .value .value "float_add" (.float x) (.float y)
  simp [hbin, floatAddSym]

instance : IntrinsicSound [floatAdd] floatAdd where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [floatAdd, mkBinFloat, List.mem_cons] at hφ
    rcases hφ with rfl | hφ
    · have hbase : (binFloatDefAxiom floatAddSym .fpAdd).wfIn (Intrinsic.sigOf [floatAdd]) := by
        simp [binFloatDefAxiom, binTerm, floatAdd, mkBinFloat, Intrinsic.sigOf, Intrinsic.foldSig,
          floatAddSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addBinary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
    · rcases hφ with rfl | hnil
      ·
        have hbase : (binFloatTypeAxiom floatAddSym).wfIn (Intrinsic.sigOf [floatAdd]) := by
          simp [binFloatTypeAxiom, binTerm, floatAdd, mkBinFloat, Intrinsic.sigOf, Intrinsic.foldSig,
            floatAddSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnPred.wfIn,
            Signature.extendWithSym, Signature.empty, Signature.addBinary,
            Signature.declVar, Signature.addVar, Signature.remove]
        exact Formula.wfIn_mono _ hbase hsub hwf
      · cases hnil
  proof := by
    intro ρ hdeps φ hφ
    simp only [floatAdd, mkBinFloat, List.mem_cons] at hφ
    have hadd : ρ.respects (some floatAddSym) := hdeps floatAdd (by simp)
    simp only [Env.respects] at hadd
    have hb : ∀ x y : Runtime.Val,
        ((ρ.updateConst .value "a" x).updateConst .value "b" y).binary
          .value .value .value "float_add" = fun a b => floatAddSym.interp (a, b) := by
      intro x y; rw [Env.updateConst_binary, Env.updateConst_binary]; simpa [floatAddSym] using hadd
    rcases hφ with rfl | hφ
    · simp only [binFloatDefAxiom, Formula.all, Formula.eval]
      intro x y
      simp [binTerm, Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb x y, floatAddSym]
      rfl
    · rcases hφ with rfl | hnil
      · simp only [binFloatTypeAxiom, Formula.all, Formula.eval]
        intro x y
        simp [binTerm, Term.eval, Env.lookupConst_updateConst_same,
          Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb x y, floatAddSym]
      · cases hnil
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono floatAdd_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars floatAdd.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [floatAdd_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.float, TinyML.Typ.float] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_l (off_shape_two_ty _ (by simp))).trans sep_elim_l
    | [_] => exact (sep_mono_l (off_shape_two_ty _ (by simp))).trans sep_elim_l
    | _ :: _ :: _ :: _ => exact (sep_mono_l (off_shape_two_ty _ (by simp))).trans sep_elim_l
    | [v1, v2] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v1 [v2] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv1, Hvs2⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ v2 [] _ _).1 $$ Hvs2
      icases Hcons2 with ⟨Hv2, _⟩
      ihave Hv1eq := (TinyML.ValHasType.float Θ v1).1 $$ Hv1
      ipure Hv1eq
      ihave Hv2eq := (TinyML.ValHasType.float Θ v2).1 $$ Hv2
      ipure Hv2eq
      obtain ⟨x, rfl⟩ := Hv1eq
      obtain ⟨y, rfl⟩ := Hv2eq
      rw [floatAdd]
      rw [mkBinFloat_toWp]
      iexists x
      iexists y
      isplitr [Hpred]
      · ipure_intro; exact ⟨rfl, rfl⟩
      · refine (assert_ret_apply Θ _ "ret" _ _ (.float (FloatBits.add x y)) ?_).trans ?_
        · exact floatAdd_assert_eval ρ x y hρ
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.float_intro Θ (FloatBits.add x y)

private theorem mkBinFloat_sound_of (sym : FOL.Symbol .two) (pathTail : String)
    (bits : UInt64 → UInt64 → UInt64) (op : BinOp .float .float .float)
    (hDefWf : (binFloatDefAxiom sym op).wfIn (Intrinsic.sigOf [mkBinFloat sym pathTail bits op]))
    (hTypeWf : (binFloatTypeAxiom sym).wfIn (Intrinsic.sigOf [mkBinFloat sym pathTail bits op]))
    (hSpecWf : PredTrans.wfIn
      ((Intrinsic.sigOf [mkBinFloat sym pathTail bits op]).declVars
        (Spec.argVars (mkBinFloat sym pathTail bits op).specArgs))
      (mkBinFloat sym pathTail bits op).spec.pred)
    (htype : ∀ a b : Runtime.Val, ∃ z : UInt64, sym.interp (a, b) = .float z)
    (hdef : ∀ (ρ : Env) (a b : Runtime.Val),
      valFloat (sym.interp (a, b)) = BinOp.eval ρ op (valFloat a) (valFloat b))
    (hbits : ∀ x y, sym.interp (.float x, .float y) = .float (bits x y)) :
    IntrinsicSound [mkBinFloat sym pathTail bits op] (mkBinFloat sym pathTail bits op) where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [mkBinFloat, List.mem_cons] at hφ
    rcases hφ with rfl | hφ
    · exact Formula.wfIn_mono _ hDefWf hsub hwf
    · rcases hφ with rfl | hnil
      · exact Formula.wfIn_mono _ hTypeWf hsub hwf
      · cases hnil
  proof := by
    intro ρ hdeps φ hφ
    simp only [mkBinFloat, List.mem_cons] at hφ
    have hs : ρ.respects (some sym) := hdeps (mkBinFloat sym pathTail bits op) (by simp)
    simp only [Env.respects] at hs
    have hb : ∀ x y : Runtime.Val,
        ((ρ.updateConst .value "a" x).updateConst .value "b" y).binary
          .value .value .value sym.name = fun a b => sym.interp (a, b) := by
      intro x y; rw [Env.updateConst_binary, Env.updateConst_binary]; exact hs
    rcases hφ with rfl | hφ
    · simp only [binFloatDefAxiom, Formula.all, Formula.eval]
      intro x y
      simp [binTerm, Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb x y]
      exact hdef _ x y
    · rcases hφ with rfl | hnil
      · simp only [binFloatTypeAxiom, Formula.all, Formula.eval]
        intro x y
        simp [binTerm, Term.eval, Env.lookupConst_updateConst_same,
          Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb x y]
        rcases htype x y with ⟨z, hz⟩
        rw [hz]
        trivial
      · cases hnil
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono hSpecWf
      (Signature.Subset.declVars hsub (Spec.argVars (mkBinFloat sym pathTail bits op).specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [mkBinFloat_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.float, TinyML.Typ.float] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_l (off_shape_two_ty _ (by simp))).trans sep_elim_l
    | [_] => exact (sep_mono_l (off_shape_two_ty _ (by simp))).trans sep_elim_l
    | _ :: _ :: _ :: _ => exact (sep_mono_l (off_shape_two_ty _ (by simp))).trans sep_elim_l
    | [v1, v2] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v1 [v2] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv1, Hvs2⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ v2 [] _ _).1 $$ Hvs2
      icases Hcons2 with ⟨Hv2, _⟩
      ihave Hv1eq := (TinyML.ValHasType.float Θ v1).1 $$ Hv1
      ipure Hv1eq
      ihave Hv2eq := (TinyML.ValHasType.float Θ v2).1 $$ Hv2
      ipure Hv2eq
      obtain ⟨x, rfl⟩ := Hv1eq
      obtain ⟨y, rfl⟩ := Hv2eq
      rw [mkBinFloat_toWp]
      iexists x
      iexists y
      isplitr [Hpred]
      · ipure_intro; exact ⟨rfl, rfl⟩
      · refine (assert_ret_apply Θ _ "ret" _ _ (.float (bits x y)) ?_).trans ?_
        ·
          have hargs := respects_argsEnv_two (mkBinFloat sym pathTail bits op).specArgs [.float x, .float y] hρ
          have hbin : (Spec.argsEnv ρ (mkBinFloat sym pathTail bits op).specArgs [.float x, .float y]).env.binary
              .value .value .value sym.name = fun a b => sym.interp (a, b) := by
            simpa [Env.respects] using hargs
          show (Formula.eq .value (.var .value "ret")
              (binTerm sym.name (.var .value "a") (.var .value "b"))).eval
            ((Spec.argsEnv ρ (mkBinFloat sym pathTail bits op).specArgs [.float x, .float y]).updateConst
              .value "ret" (.float (bits x y))).env
          show Runtime.Val.float (bits x y) =
            (Spec.argsEnv ρ (mkBinFloat sym pathTail bits op).specArgs [.float x, .float y]).env.binary
              .value .value .value sym.name (.float x) (.float y)
          simp [hbin, hbits x y]
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.float_intro Θ (bits x y)

/-- Soundness for a `mkBinFloatWith` intrinsic. Identical to `mkBinFloat_sound_of`
except the definitional axiom is opaque: the caller supplies `hdefcase`, which
discharges `Formula.eval ρ defAxiom` given the binary-symbol interpretation `hb`. -/
private theorem mkBinFloatWith_sound_of (sym : FOL.Symbol .two) (pathTail : String)
    (bits : UInt64 → UInt64 → UInt64) (defAxiom : Formula)
    (hDefWf : defAxiom.wfIn (Intrinsic.sigOf [mkBinFloatWith sym pathTail bits defAxiom]))
    (hTypeWf : (binFloatTypeAxiom sym).wfIn (Intrinsic.sigOf [mkBinFloatWith sym pathTail bits defAxiom]))
    (hSpecWf : PredTrans.wfIn
      ((Intrinsic.sigOf [mkBinFloatWith sym pathTail bits defAxiom]).declVars
        (Spec.argVars (mkBinFloatWith sym pathTail bits defAxiom).specArgs))
      (mkBinFloatWith sym pathTail bits defAxiom).spec.pred)
    (htype : ∀ a b : Runtime.Val, ∃ z : UInt64, sym.interp (a, b) = .float z)
    (hbits : ∀ x y, sym.interp (.float x, .float y) = .float (bits x y))
    (hdefcase : ∀ ρ : Env,
      (∀ x y : Runtime.Val, ((ρ.updateConst .value "a" x).updateConst .value "b" y).binary
          .value .value .value sym.name = fun a b => sym.interp (a, b)) →
      Formula.eval ρ defAxiom) :
    IntrinsicSound [mkBinFloatWith sym pathTail bits defAxiom] (mkBinFloatWith sym pathTail bits defAxiom) where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [mkBinFloatWith, List.mem_cons] at hφ
    rcases hφ with rfl | hφ
    · exact Formula.wfIn_mono _ hDefWf hsub hwf
    · rcases hφ with rfl | hnil
      · exact Formula.wfIn_mono _ hTypeWf hsub hwf
      · cases hnil
  proof := by
    intro ρ hdeps φ hφ
    simp only [mkBinFloatWith, List.mem_cons] at hφ
    have hs : ρ.respects (some sym) := hdeps (mkBinFloatWith sym pathTail bits defAxiom) (by simp)
    simp only [Env.respects] at hs
    have hb : ∀ x y : Runtime.Val,
        ((ρ.updateConst .value "a" x).updateConst .value "b" y).binary
          .value .value .value sym.name = fun a b => sym.interp (a, b) := by
      intro x y; rw [Env.updateConst_binary, Env.updateConst_binary]; exact hs
    rcases hφ with rfl | hφ
    · exact hdefcase ρ hb
    · rcases hφ with rfl | hnil
      · simp only [binFloatTypeAxiom, Formula.all, Formula.eval]
        intro x y
        simp [binTerm, Term.eval, Env.lookupConst_updateConst_same,
          Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb x y]
        rcases htype x y with ⟨z, hz⟩
        rw [hz]
        trivial
      · cases hnil
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono hSpecWf
      (Signature.Subset.declVars hsub (Spec.argVars (mkBinFloatWith sym pathTail bits defAxiom).specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [mkBinFloatWith_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.float, TinyML.Typ.float] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_l (off_shape_two_ty _ (by simp))).trans sep_elim_l
    | [_] => exact (sep_mono_l (off_shape_two_ty _ (by simp))).trans sep_elim_l
    | _ :: _ :: _ :: _ => exact (sep_mono_l (off_shape_two_ty _ (by simp))).trans sep_elim_l
    | [v1, v2] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v1 [v2] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv1, Hvs2⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ v2 [] _ _).1 $$ Hvs2
      icases Hcons2 with ⟨Hv2, _⟩
      ihave Hv1eq := (TinyML.ValHasType.float Θ v1).1 $$ Hv1
      ipure Hv1eq
      ihave Hv2eq := (TinyML.ValHasType.float Θ v2).1 $$ Hv2
      ipure Hv2eq
      obtain ⟨x, rfl⟩ := Hv1eq
      obtain ⟨y, rfl⟩ := Hv2eq
      rw [mkBinFloatWith_toWp]
      iexists x
      iexists y
      isplitr [Hpred]
      · ipure_intro; exact ⟨rfl, rfl⟩
      · refine (assert_ret_apply Θ _ "ret" _ _ (.float (bits x y)) ?_).trans ?_
        ·
          have hargs := respects_argsEnv_two (mkBinFloatWith sym pathTail bits defAxiom).specArgs [.float x, .float y] hρ
          have hbin : (Spec.argsEnv ρ (mkBinFloatWith sym pathTail bits defAxiom).specArgs [.float x, .float y]).env.binary
              .value .value .value sym.name = fun a b => sym.interp (a, b) := by
            simpa [Env.respects] using hargs
          show (Formula.eq .value (.var .value "ret")
              (binTerm sym.name (.var .value "a") (.var .value "b"))).eval
            ((Spec.argsEnv ρ (mkBinFloatWith sym pathTail bits defAxiom).specArgs [.float x, .float y]).updateConst
              .value "ret" (.float (bits x y))).env
          show Runtime.Val.float (bits x y) =
            (Spec.argsEnv ρ (mkBinFloatWith sym pathTail bits defAxiom).specArgs [.float x, .float y]).env.binary
              .value .value .value sym.name (.float x) (.float y)
          simp [hbin, hbits x y]
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.float_intro Θ (bits x y)

instance : IntrinsicSound [floatSub] floatSub :=
  mkBinFloat_sound_of floatSubSym "sub" FloatBits.sub .fpSub
    (by
      simp [binFloatDefAxiom, binTerm, mkBinFloat, Intrinsic.sigOf, Intrinsic.foldSig,
        floatSubSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by
      simp [binFloatTypeAxiom, binTerm, mkBinFloat, Intrinsic.sigOf, Intrinsic.foldSig,
        floatSubSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnPred.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by apply PredTrans.checkWf_ok; rfl)
    (by intro a b; exact ⟨FloatBits.sub (valFloat a) (valFloat b), rfl⟩)
    (by intros; rfl)
    (by intros; rfl)

instance : IntrinsicSound [floatMul] floatMul :=
  mkBinFloat_sound_of floatMulSym "mul" FloatBits.mul .fpMul
    (by
      simp [binFloatDefAxiom, binTerm, mkBinFloat, Intrinsic.sigOf, Intrinsic.foldSig,
        floatMulSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by
      simp [binFloatTypeAxiom, binTerm, mkBinFloat, Intrinsic.sigOf, Intrinsic.foldSig,
        floatMulSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnPred.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by apply PredTrans.checkWf_ok; rfl)
    (by intro a b; exact ⟨FloatBits.mul (valFloat a) (valFloat b), rfl⟩)
    (by intros; rfl)
    (by intros; rfl)

instance : IntrinsicSound [floatDiv] floatDiv :=
  mkBinFloat_sound_of floatDivSym "div" FloatBits.div .fpDiv
    (by
      simp [binFloatDefAxiom, binTerm, mkBinFloat, Intrinsic.sigOf, Intrinsic.foldSig,
        floatDivSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by
      simp [binFloatTypeAxiom, binTerm, mkBinFloat, Intrinsic.sigOf, Intrinsic.foldSig,
        floatDivSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnPred.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by apply PredTrans.checkWf_ok; rfl)
    (by intro a b; exact ⟨FloatBits.div (valFloat a) (valFloat b), rfl⟩)
    (by intros; rfl)
    (by intros; rfl)

instance : IntrinsicSound [floatMin] floatMin :=
  mkBinFloatWith_sound_of floatMinSym "min" FloatBits.min floatMinDefAxiom
    (by
      simp [floatMinDefAxiom, binTerm, mkBinFloatWith, Intrinsic.sigOf, Intrinsic.foldSig,
        floatMinSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn, Const.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by
      simp [binFloatTypeAxiom, binTerm, mkBinFloatWith, Intrinsic.sigOf, Intrinsic.foldSig,
        floatMinSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnPred.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by apply PredTrans.checkWf_ok; rfl)
    (by intro a b; exact ⟨FloatBits.min (valFloat a) (valFloat b), rfl⟩)
    (by intros; rfl)
    (by
      intro ρ hb
      simp only [floatMinSym_name] at hb
      simp only [floatMinDefAxiom, Formula.all, Formula.eval]
      intro x y
      simp [binTerm, Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb x y, floatMinSym,
        FloatBits.min]
      rfl)

instance : IntrinsicSound [floatMax] floatMax :=
  mkBinFloatWith_sound_of floatMaxSym "max" FloatBits.max floatMaxDefAxiom
    (by
      simp [floatMaxDefAxiom, binTerm, mkBinFloatWith, Intrinsic.sigOf, Intrinsic.foldSig,
        floatMaxSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn, Const.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by
      simp [binFloatTypeAxiom, binTerm, mkBinFloatWith, Intrinsic.sigOf, Intrinsic.foldSig,
        floatMaxSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnPred.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by apply PredTrans.checkWf_ok; rfl)
    (by intro a b; exact ⟨FloatBits.max (valFloat a) (valFloat b), rfl⟩)
    (by intros; rfl)
    (by
      intro ρ hb
      simp only [floatMaxSym_name] at hb
      simp only [floatMaxDefAxiom, Formula.all, Formula.eval]
      intro x y
      simp [binTerm, Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb x y, floatMaxSym,
        FloatBits.max]
      rfl)

/-! ## Binary `float → float → bool` intrinsics -/

private def binFloatBoolDefAxiom (sym : FOL.Symbol .two) (op : BinOp .float .float .bool) : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm sym.name (.var .value "a") (.var .value "b"))] <|
    .eq .bool (.unop .toBool (binTerm sym.name (.var .value "a") (.var .value "b")))
      (.binop op (.unop .toFloat (.var .value "a")) (.unop .toFloat (.var .value "b")))

private def binFloatBoolTypeAxiom (sym : FOL.Symbol .two) : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (binTerm sym.name (.var .value "a") (.var .value "b"))] <|
    .unpred .isBool (binTerm sym.name (.var .value "a") (.var .value "b"))

private def mkBinFloatBool (sym : FOL.Symbol .two) (pathTail : String)
    (bits : UInt64 → UInt64 → Bool) (op : BinOp .float .float .bool) : Intrinsic where
  arity  := .two
  name   := sym.name
  path   := some ("Float", [pathTail])
  reduce := fun (a, b) v => ∃ x y : UInt64, a = .float x ∧ b = .float y ∧ v = .bool (bits x y)
  wp     := fun (a, b) Q => iprop(∃ x y : UInt64, ⌜a = .float x ∧ b = .float y⌝ ∗ Q (.bool (bits x y)))
  spec   :=
    { args  := [("a", .float), ("b", .float)]
      retTy := .bool
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") (binTerm sym.name (.var .value "a") (.var .value "b"))) (.ret ())) }
  folSym := some sym
  axioms := [binFloatBoolDefAxiom sym op, binFloatBoolTypeAxiom sym]

@[simp] theorem mkBinFloatBool_arity (sym : FOL.Symbol .two) (pathTail bits op) :
    (mkBinFloatBool sym pathTail bits op).arity = .two := rfl
@[simp] theorem mkBinFloatBool_folSym (sym : FOL.Symbol .two) (pathTail bits op) :
    (mkBinFloatBool sym pathTail bits op).folSym = some sym := rfl
@[simp] theorem mkBinFloatBool_toWp (sym : FOL.Symbol .two) (pathTail bits op)
    (a b : Runtime.Val) (Q : Runtime.Val → iProp) :
    (mkBinFloatBool sym pathTail bits op).toWp [a, b] Q =
      iprop(∃ x y : UInt64, ⌜a = .float x ∧ b = .float y⌝ ∗ Q (.bool (bits x y))) :=
  Intrinsic.toWp_two_of_arity _ _ _ _ _ _ _ _ _ Q

def floatEqual : Intrinsic := mkBinFloatBool floatEqualSym "equal" FloatBits.eq .fpEq
def floatLt : Intrinsic := mkBinFloatBool floatLtSym "lt" FloatBits.lt .fpLt
def floatLe : Intrinsic := mkBinFloatBool floatLeSym "le" FloatBits.le .fpLe

@[simp] theorem floatEqual_arity : floatEqual.arity = .two := rfl
@[simp] theorem floatLt_arity : floatLt.arity = .two := rfl
@[simp] theorem floatLe_arity : floatLe.arity = .two := rfl
@[simp] theorem floatEqual_folSym : floatEqual.folSym = some floatEqualSym := rfl
@[simp] theorem floatLt_folSym : floatLt.folSym = some floatLtSym := rfl
@[simp] theorem floatLe_folSym : floatLe.folSym = some floatLeSym := rfl

private theorem mkBinFloatBool_sound_of (sym : FOL.Symbol .two) (pathTail : String)
    (bits : UInt64 → UInt64 → Bool) (op : BinOp .float .float .bool)
    (hDefWf : (binFloatBoolDefAxiom sym op).wfIn (Intrinsic.sigOf [mkBinFloatBool sym pathTail bits op]))
    (hTypeWf : (binFloatBoolTypeAxiom sym).wfIn (Intrinsic.sigOf [mkBinFloatBool sym pathTail bits op]))
    (hSpecWf : PredTrans.wfIn
      ((Intrinsic.sigOf [mkBinFloatBool sym pathTail bits op]).declVars
        (Spec.argVars (mkBinFloatBool sym pathTail bits op).specArgs))
      (mkBinFloatBool sym pathTail bits op).spec.pred)
    (htype : ∀ a b : Runtime.Val, ∃ z : Bool, sym.interp (a, b) = .bool z)
    (hdef : ∀ (ρ : Env) (a b : Runtime.Val),
      valBool (sym.interp (a, b)) = BinOp.eval ρ op (valFloat a) (valFloat b))
    (hbits : ∀ x y, sym.interp (.float x, .float y) = .bool (bits x y)) :
    IntrinsicSound [mkBinFloatBool sym pathTail bits op] (mkBinFloatBool sym pathTail bits op) where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [mkBinFloatBool, List.mem_cons] at hφ
    rcases hφ with rfl | hφ
    · exact Formula.wfIn_mono _ hDefWf hsub hwf
    · rcases hφ with rfl | hnil
      · exact Formula.wfIn_mono _ hTypeWf hsub hwf
      · cases hnil
  proof := by
    intro ρ hdeps φ hφ
    simp only [mkBinFloatBool, List.mem_cons] at hφ
    have hs : ρ.respects (some sym) := hdeps (mkBinFloatBool sym pathTail bits op) (by simp)
    simp only [Env.respects] at hs
    have hb : ∀ x y : Runtime.Val,
        ((ρ.updateConst .value "a" x).updateConst .value "b" y).binary
          .value .value .value sym.name = fun a b => sym.interp (a, b) := by
      intro x y; rw [Env.updateConst_binary, Env.updateConst_binary]; exact hs
    rcases hφ with rfl | hφ
    · simp only [binFloatBoolDefAxiom, Formula.all, Formula.eval]
      intro x y
      simp [binTerm, Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb x y]
      exact hdef _ x y
    · rcases hφ with rfl | hnil
      · simp only [binFloatBoolTypeAxiom, Formula.all, Formula.eval]
        intro x y
        simp [binTerm, Term.eval, Env.lookupConst_updateConst_same,
          Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb x y]
        rcases htype x y with ⟨z, hz⟩
        rw [hz]
        trivial
      · cases hnil
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono hSpecWf
      (Signature.Subset.declVars hsub (Spec.argVars (mkBinFloatBool sym pathTail bits op).specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [mkBinFloatBool_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.float, TinyML.Typ.float] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_l (off_shape_two_ty _ (by simp))).trans sep_elim_l
    | [_] => exact (sep_mono_l (off_shape_two_ty _ (by simp))).trans sep_elim_l
    | _ :: _ :: _ :: _ => exact (sep_mono_l (off_shape_two_ty _ (by simp))).trans sep_elim_l
    | [v1, v2] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v1 [v2] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv1, Hvs2⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ v2 [] _ _).1 $$ Hvs2
      icases Hcons2 with ⟨Hv2, _⟩
      ihave Hv1eq := (TinyML.ValHasType.float Θ v1).1 $$ Hv1
      ipure Hv1eq
      ihave Hv2eq := (TinyML.ValHasType.float Θ v2).1 $$ Hv2
      ipure Hv2eq
      obtain ⟨x, rfl⟩ := Hv1eq
      obtain ⟨y, rfl⟩ := Hv2eq
      rw [mkBinFloatBool_toWp]
      iexists x
      iexists y
      isplitr [Hpred]
      · ipure_intro; exact ⟨rfl, rfl⟩
      · refine (assert_ret_apply Θ _ "ret" _ _ (.bool (bits x y)) ?_).trans ?_
        ·
          have hargs := respects_argsEnv_two (mkBinFloatBool sym pathTail bits op).specArgs [.float x, .float y] hρ
          have hbin : (Spec.argsEnv ρ (mkBinFloatBool sym pathTail bits op).specArgs [.float x, .float y]).env.binary
              .value .value .value sym.name = fun a b => sym.interp (a, b) := by
            simpa [Env.respects] using hargs
          show (Formula.eq .value (.var .value "ret")
              (binTerm sym.name (.var .value "a") (.var .value "b"))).eval
            ((Spec.argsEnv ρ (mkBinFloatBool sym pathTail bits op).specArgs [.float x, .float y]).updateConst
              .value "ret" (.bool (bits x y))).env
          show Runtime.Val.bool (bits x y) =
            (Spec.argsEnv ρ (mkBinFloatBool sym pathTail bits op).specArgs [.float x, .float y]).env.binary
              .value .value .value sym.name (.float x) (.float y)
          simp [hbin, hbits x y]
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.bool_intro Θ (bits x y)

instance : IntrinsicSound [floatEqual] floatEqual :=
  mkBinFloatBool_sound_of floatEqualSym "equal" FloatBits.eq .fpEq
    (by
      simp [binFloatBoolDefAxiom, binTerm, mkBinFloatBool, Intrinsic.sigOf, Intrinsic.foldSig,
        floatEqualSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by
      simp [binFloatBoolTypeAxiom, binTerm, mkBinFloatBool, Intrinsic.sigOf, Intrinsic.foldSig,
        floatEqualSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnPred.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by apply PredTrans.checkWf_ok; rfl)
    (by intro a b; exact ⟨FloatBits.eq (valFloat a) (valFloat b), rfl⟩)
    (by intros; rfl)
    (by intros; rfl)

instance : IntrinsicSound [floatLt] floatLt :=
  mkBinFloatBool_sound_of floatLtSym "lt" FloatBits.lt .fpLt
    (by
      simp [binFloatBoolDefAxiom, binTerm, mkBinFloatBool, Intrinsic.sigOf, Intrinsic.foldSig,
        floatLtSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by
      simp [binFloatBoolTypeAxiom, binTerm, mkBinFloatBool, Intrinsic.sigOf, Intrinsic.foldSig,
        floatLtSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnPred.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by apply PredTrans.checkWf_ok; rfl)
    (by intro a b; exact ⟨FloatBits.lt (valFloat a) (valFloat b), rfl⟩)
    (by intros; rfl)
    (by intros; rfl)

instance : IntrinsicSound [floatLe] floatLe :=
  mkBinFloatBool_sound_of floatLeSym "le" FloatBits.le .fpLe
    (by
      simp [binFloatBoolDefAxiom, binTerm, mkBinFloatBool, Intrinsic.sigOf, Intrinsic.foldSig,
        floatLeSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by
      simp [binFloatBoolTypeAxiom, binTerm, mkBinFloatBool, Intrinsic.sigOf, Intrinsic.foldSig,
        floatLeSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnPred.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove])
    (by apply PredTrans.checkWf_ok; rfl)
    (by intro a b; exact ⟨FloatBits.le (valFloat a) (valFloat b), rfl⟩)
    (by intros; rfl)
    (by intros; rfl)

/-! ## Arity-zero float constants -/

private def zeroFloatDefAxiom (sym : FOL.Symbol .zero) (c : Const .float) : Formula :=
  .eq .float (.unop .toFloat (constTerm sym.name)) (.const c)

private def zeroFloatTypeAxiom (sym : FOL.Symbol .zero) : Formula :=
  .unpred .isFloat (constTerm sym.name)

private def mkZeroFloat (sym : FOL.Symbol .zero) (pathTail : String)
    (bits : UInt64) (c : Const .float) : Intrinsic where
  arity  := .zero
  name   := sym.name
  path   := some ("Float", [pathTail])
  reduce := fun () v => v = .float bits
  wp     := fun () Q => Q (.float bits)
  spec   :=
    { args  := []
      retTy := .float
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") (constTerm sym.name)) (.ret ())) }
  folSym := some sym
  axioms := [zeroFloatDefAxiom sym c, zeroFloatTypeAxiom sym]

@[simp] theorem mkZeroFloat_arity (sym : FOL.Symbol .zero) (pathTail bits c) :
    (mkZeroFloat sym pathTail bits c).arity = .zero := rfl
@[simp] theorem mkZeroFloat_folSym (sym : FOL.Symbol .zero) (pathTail bits c) :
    (mkZeroFloat sym pathTail bits c).folSym = some sym := rfl
@[simp] theorem mkZeroFloat_toWp (sym : FOL.Symbol .zero) (pathTail bits c)
    (Q : Runtime.Val → iProp) :
    (mkZeroFloat sym pathTail bits c).toWp [] Q = Q (.float bits) :=
  Intrinsic.toWp_zero_of_arity _ _ _ _ _ _ _ Q

def floatNan : Intrinsic := mkZeroFloat floatNanSym "nan" FloatBits.nan .fpNaN
def floatInfinity : Intrinsic := mkZeroFloat floatInfinitySym "infinity" FloatBits.posInf .fpPosInf
def floatNegInfinity : Intrinsic := mkZeroFloat floatNegInfinitySym "neg_infinity" FloatBits.negInf .fpNegInf

@[simp] theorem floatNan_arity : floatNan.arity = .zero := rfl
@[simp] theorem floatInfinity_arity : floatInfinity.arity = .zero := rfl
@[simp] theorem floatNegInfinity_arity : floatNegInfinity.arity = .zero := rfl
@[simp] theorem floatNan_folSym : floatNan.folSym = some floatNanSym := rfl
@[simp] theorem floatInfinity_folSym : floatInfinity.folSym = some floatInfinitySym := rfl
@[simp] theorem floatNegInfinity_folSym : floatNegInfinity.folSym = some floatNegInfinitySym := rfl

private theorem mkZeroFloat_sound_of (sym : FOL.Symbol .zero) (pathTail : String)
    (bits : UInt64) (c : Const .float)
    (hname : sym.name ≠ "ret")
    (hinterp : sym.interp () = .float bits)
    (hconst : ∀ ρ : Env, Const.denote ρ c = bits)
    (hDefWf : (zeroFloatDefAxiom sym c).wfIn (Intrinsic.sigOf [mkZeroFloat sym pathTail bits c]))
    (hTypeWf : (zeroFloatTypeAxiom sym).wfIn (Intrinsic.sigOf [mkZeroFloat sym pathTail bits c]))
    (hSpecWf : PredTrans.wfIn
      ((Intrinsic.sigOf [mkZeroFloat sym pathTail bits c]).declVars
        (Spec.argVars (mkZeroFloat sym pathTail bits c).specArgs))
      (mkZeroFloat sym pathTail bits c).spec.pred) :
    IntrinsicSound [mkZeroFloat sym pathTail bits c] (mkZeroFloat sym pathTail bits c) where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [mkZeroFloat, List.mem_cons] at hφ
    rcases hφ with rfl | hφ
    · exact Formula.wfIn_mono _ hDefWf hsub hwf
    · rcases hφ with rfl | hnil
      · exact Formula.wfIn_mono _ hTypeWf hsub hwf
      · cases hnil
  proof := by
    intro ρ hdeps φ hφ
    simp only [mkZeroFloat, List.mem_cons] at hφ
    have hs : ρ.respects (some sym) := hdeps (mkZeroFloat sym pathTail bits c) (by simp)
    simp only [Env.respects] at hs
    rcases hφ with rfl | hφ
    · simp only [zeroFloatDefAxiom, Formula.eval, Term.eval, UnOp.eval]
      show valFloat (ρ.lookupConst .value sym.name) = Const.denote ρ c
      rw [hs, hinterp, hconst ρ]
      rfl
    · rcases hφ with rfl | hnil
      · simp only [zeroFloatTypeAxiom, Formula.eval, UnPred.eval]
        change match ρ.lookupConst .value sym.name with | .float _ => True | _ => False
        rw [hs, hinterp]
        trivial
      · cases hnil
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono hSpecWf
      (Signature.Subset.declVars hsub (Spec.argVars (mkZeroFloat sym pathTail bits c).specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [mkZeroFloat_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [] ∗ _ ⊢ _
    match vs with
    | _ :: _ => exact (sep_mono_l (off_shape_zero _ (by simp))).trans sep_elim_l
    | [] =>
      rw [mkZeroFloat_toWp]
      refine (sep_mono_l (TinyML.ValsHaveTypes.nil Θ).1).trans ?_
      refine emp_sep.1.trans ?_
      refine (assert_ret_apply Θ _ "ret" _ _ (.float bits) ?_).trans ?_
      · show Runtime.Val.float bits = (ρ.updateConst .value "ret" (.float bits)).env.lookupConst .value sym.name
        rw [VerifM.Env.updateConst_env]
        rw [Env.lookupConst_updateConst_ne hname]
        exact (hρ.trans hinterp).symm
      · iintro Hwand
        iapply Hwand
        exact TinyML.ValHasType.float_intro Θ bits

instance : IntrinsicSound [floatNan] floatNan :=
  mkZeroFloat_sound_of floatNanSym "nan" FloatBits.nan .fpNaN (by decide) rfl (by intro ρ; rfl)
    (by
      simp [zeroFloatDefAxiom, constTerm, mkZeroFloat, Intrinsic.sigOf, Intrinsic.foldSig,
        floatNanSym, Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addConst])
    (by
      simp [zeroFloatTypeAxiom, constTerm, mkZeroFloat, Intrinsic.sigOf, Intrinsic.foldSig,
        floatNanSym, Formula.wfIn, Term.wfIn, Const.wfIn, UnPred.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addConst])
    (by apply PredTrans.checkWf_ok; rfl)

instance : IntrinsicSound [floatInfinity] floatInfinity :=
  mkZeroFloat_sound_of floatInfinitySym "infinity" FloatBits.posInf .fpPosInf (by decide) rfl (by intro ρ; rfl)
    (by
      simp [zeroFloatDefAxiom, constTerm, mkZeroFloat, Intrinsic.sigOf, Intrinsic.foldSig,
        floatInfinitySym, Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addConst])
    (by
      simp [zeroFloatTypeAxiom, constTerm, mkZeroFloat, Intrinsic.sigOf, Intrinsic.foldSig,
        floatInfinitySym, Formula.wfIn, Term.wfIn, Const.wfIn, UnPred.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addConst])
    (by apply PredTrans.checkWf_ok; rfl)

instance : IntrinsicSound [floatNegInfinity] floatNegInfinity :=
  mkZeroFloat_sound_of floatNegInfinitySym "neg_infinity" FloatBits.negInf .fpNegInf (by decide) rfl (by intro ρ; rfl)
    (by
      simp [zeroFloatDefAxiom, constTerm, mkZeroFloat, Intrinsic.sigOf, Intrinsic.foldSig,
        floatNegInfinitySym, Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addConst])
    (by
      simp [zeroFloatTypeAxiom, constTerm, mkZeroFloat, Intrinsic.sigOf, Intrinsic.foldSig,
        floatNegInfinitySym, Formula.wfIn, Term.wfIn, Const.wfIn, UnPred.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addConst])
    (by apply PredTrans.checkWf_ok; rfl)

end Intrinsics
end Stdlib

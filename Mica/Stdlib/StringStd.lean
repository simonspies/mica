-- SUMMARY: Byte-string intrinsics (`String.length`, `cat`, `equal`, `starts_with`, `ends_with`) and soundness instances.
import Mica.Stdlib.IntStd

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-- String projection of a runtime value, matching FOL's `toString`. -/
private def valStr : Runtime.Val → List UInt8
  | .str s => s
  | _      => []

@[simp] private theorem valStr_str (s : List UInt8) : valStr (.str s) = s := rfl

@[simp] private theorem toString_eq_valStr (ρ : Env) (v : Runtime.Val) :
    UnOp.eval ρ .toString v = valStr v := rfl

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
projection, not that the result *is* an integer value. -/

def stringLengthDefAxiom : Formula :=
  .forall_ "s" .value <|
    .eq .int
      (.unop .toInt (stringLengthTerm (.var .value "s")))
      (.unop .seqLen (.unop .toString (.var .value "s")))

def stringLengthTypeAxiom : Formula :=
  .forall_ "s" .value <| .unpred .isInt (stringLengthTerm (.var .value "s"))

def stringCatDefAxiom : Formula :=
  .forall_ "a" .value <| .forall_ "b" .value <|
    .eq .string
      (.unop .toString (stringCatTerm (.var .value "a") (.var .value "b")))
      (.binop .seqConcat (.unop .toString (.var .value "a")) (.unop .toString (.var .value "b")))

def stringCatTypeAxiom : Formula :=
  .forall_ "a" .value <| .forall_ "b" .value <|
    .unpred .isStr (stringCatTerm (.var .value "a") (.var .value "b"))

def stringEqualDefAxiom : Formula :=
  .forall_ "a" .value <| .forall_ "b" .value <|
    .eq .bool
      (.unop .toBool (stringEqualTerm (.var .value "a") (.var .value "b")))
      (.binop (.eq (τ := .string)) (.unop .toString (.var .value "a")) (.unop .toString (.var .value "b")))

def stringEqualTypeAxiom : Formula :=
  .forall_ "a" .value <| .forall_ "b" .value <|
    .unpred .isBool (stringEqualTerm (.var .value "a") (.var .value "b"))

def stringStartsWithDefAxiom : Formula :=
  .forall_ "prefix" .value <| .forall_ "s" .value <|
    .eq .bool
      (.unop .toBool (stringStartsWithTerm (.var .value "prefix") (.var .value "s")))
      (.binop .seqPrefixOf (.unop .toString (.var .value "prefix")) (.unop .toString (.var .value "s")))

def stringStartsWithTypeAxiom : Formula :=
  .forall_ "prefix" .value <| .forall_ "s" .value <|
    .unpred .isBool (stringStartsWithTerm (.var .value "prefix") (.var .value "s"))

def stringEndsWithDefAxiom : Formula :=
  .forall_ "suffix" .value <| .forall_ "s" .value <|
    .eq .bool
      (.unop .toBool (stringEndsWithTerm (.var .value "suffix") (.var .value "s")))
      (.binop .seqSuffixOf (.unop .toString (.var .value "suffix")) (.unop .toString (.var .value "s")))

def stringEndsWithTypeAxiom : Formula :=
  .forall_ "suffix" .value <| .forall_ "s" .value <|
    .unpred .isBool (stringEndsWithTerm (.var .value "suffix") (.var .value "s"))

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

/-- `String.length`: byte length. -/
def stringLength : Intrinsic where
  arity    := .one
  name     := "string_length"
  path     := some ("String", ["length"])
  reduce   := fun a v => ∃ s : List UInt8, a = .str s ∧ v = .int s.length
  wp       := fun a Q => iprop(∃ s : List UInt8, ⌜a = .str s⌝ ∗ Q (.int s.length))
  spec     :=
    { args  := [("s", .string)]
      retTy := .int
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") (stringLengthTerm (.var .value "s")))
          (.ret ())) }
  folSym   := some stringLengthSym
  axioms   := [stringLengthDefAxiom, stringLengthTypeAxiom]

@[simp] theorem stringLength_arity : stringLength.arity = .one := rfl
@[simp] theorem stringLength_folSym : stringLength.folSym = some stringLengthSym := rfl
@[simp] theorem stringLength_toWp (a : Runtime.Val) (Q : Runtime.Val → iProp) :
    stringLength.toWp [a] Q =
      iprop(∃ s : List UInt8, ⌜a = .str s⌝ ∗ Q (.int s.length)) :=
  Intrinsic.toWp_one_of_arity _ _ _ _ _ _ _ _ Q

private theorem stringLength_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [stringLength]).declVars (Spec.argVars stringLength.specArgs)) stringLength.spec.pred := by
  apply PredTrans.checkWf_ok
  rfl

private theorem stringLength_assert_eval (ρ : VerifM.Env) (s : List UInt8)
    (hρ : ρ.env.respects (some stringLengthSym)) :
    (Formula.eq .value (.var .value "ret") (stringLengthTerm (.var .value "s"))).eval
      ((Spec.argsEnv ρ stringLength.specArgs [.str s]).updateConst .value "ret" (.int s.length)).env := by
  have hargs := respects_argsEnv_one stringLength.specArgs [.str s] hρ
  have hun : (Spec.argsEnv ρ stringLength.specArgs [.str s]).env.unary
      .value .value "string_length" = stringLengthSym.interp := by
    simpa [Env.respects, stringLengthSym] using hargs
  show Runtime.Val.int s.length =
    (Spec.argsEnv ρ stringLength.specArgs [.str s]).env.unary .value .value "string_length" (.str s)
  simp [hun, stringLengthSym]

instance : IntrinsicSound [stringLength] stringLength where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [stringLength, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · have hbase : stringLengthDefAxiom.wfIn (Intrinsic.sigOf [stringLength]) := by
        simp [stringLengthDefAxiom, stringLengthTerm, Intrinsic.sigOf, Intrinsic.foldSig,
          stringLength, stringLengthSym, Formula.wfIn, Term.wfIn, UnOp.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
    · have hbase : stringLengthTypeAxiom.wfIn (Intrinsic.sigOf [stringLength]) := by
        simp [stringLengthTypeAxiom, stringLengthTerm, Intrinsic.sigOf, Intrinsic.foldSig,
          stringLength, stringLengthSym, Formula.wfIn, Term.wfIn, UnOp.wfIn, UnPred.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addUnary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [stringLength, List.mem_cons, List.not_mem_nil, or_false] at hφ
    have hlen : ρ.respects (some stringLengthSym) := hdeps stringLength (by simp)
    simp only [Env.respects] at hlen
    have hu : ∀ s : Runtime.Val,
        (ρ.updateConst .value "s" s).unary .value .value "string_length" = stringLengthSym.interp := by
      intro s; rw [Env.updateConst_unary]; simpa [stringLengthSym] using hlen
    rcases hφ with rfl | rfl
    · simp only [stringLengthDefAxiom, Formula.eval]
      intro s
      simp [stringLengthTerm, Term.eval, Env.lookupConst_updateConst_same, hu s,
        stringLengthSym, valStr]
      rfl
    · simp only [stringLengthTypeAxiom, Formula.eval]
      intro s
      simp [stringLengthTerm, Term.eval, Env.lookupConst_updateConst_same, hu s,
        stringLengthSym, valStr]
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono stringLength_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars stringLength.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [stringLength_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.string] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | _ :: _ :: _ => exact (sep_mono_l (off_shape_one _ (by simp))).trans sep_elim_l
    | [v] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, _⟩
      ihave Hveq := (TinyML.ValHasType.string Θ v).1 $$ Hv
      ipure Hveq
      obtain ⟨s, rfl⟩ := Hveq
      rw [stringLength_toWp]
      iexists s
      isplitr [Hpred]
      · ipure_intro; rfl
      · refine (assert_ret_apply Θ _ "ret" _ _ (.int s.length) ?_).trans ?_
        · exact stringLength_assert_eval ρ s hρ
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.int_intro Θ s.length

/-- `String.cat`: byte-string concatenation. -/
def stringCat : Intrinsic where
  arity    := .two
  name     := "string_cat"
  path     := some ("String", ["cat"])
  reduce   := fun (a, b) v => ∃ x y : List UInt8, a = .str x ∧ b = .str y ∧ v = .str (x ++ y)
  wp       := fun (a, b) Q => iprop(∃ x y : List UInt8, ⌜a = .str x ∧ b = .str y⌝ ∗ Q (.str (x ++ y)))
  spec     :=
    { args  := [("a", .string), ("b", .string)]
      retTy := .string
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (stringCatTerm (.var .value "a") (.var .value "b")))
          (.ret ())) }
  folSym   := some stringCatSym
  axioms   := [stringCatDefAxiom, stringCatTypeAxiom]

@[simp] theorem stringCat_arity : stringCat.arity = .two := rfl
@[simp] theorem stringCat_folSym : stringCat.folSym = some stringCatSym := rfl
@[simp] theorem stringCat_toWp (a b : Runtime.Val) (Q : Runtime.Val → iProp) :
    stringCat.toWp [a, b] Q =
      iprop(∃ x y : List UInt8, ⌜a = .str x ∧ b = .str y⌝ ∗ Q (.str (x ++ y))) :=
  Intrinsic.toWp_two_of_arity _ _ _ _ _ _ _ _ _ Q

private theorem stringCat_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [stringCat]).declVars (Spec.argVars stringCat.specArgs)) stringCat.spec.pred := by
  apply PredTrans.checkWf_ok
  rfl

private theorem stringCat_assert_eval (ρ : VerifM.Env) (x y : List UInt8)
    (hρ : ρ.env.respects (some stringCatSym)) :
    (Formula.eq .value (.var .value "ret")
      (stringCatTerm (.var .value "a") (.var .value "b"))).eval
      ((Spec.argsEnv ρ stringCat.specArgs [.str x, .str y]).updateConst
        .value "ret" (.str (x ++ y))).env := by
  have hargs := respects_argsEnv_two stringCat.specArgs [.str x, .str y] hρ
  have hbin : (Spec.argsEnv ρ stringCat.specArgs [.str x, .str y]).env.binary
      .value .value .value "string_cat" = fun a b => stringCatSym.interp (a, b) := by
    simpa [Env.respects, stringCatSym] using hargs
  show Runtime.Val.str (x ++ y) =
    (Spec.argsEnv ρ stringCat.specArgs [.str x, .str y]).env.binary
      .value .value .value "string_cat" (.str x) (.str y)
  simp [hbin, stringCatSym]

instance : IntrinsicSound [stringCat] stringCat where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [stringCat, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · have hbase : stringCatDefAxiom.wfIn (Intrinsic.sigOf [stringCat]) := by
        simp [stringCatDefAxiom, stringCatTerm, Intrinsic.sigOf, Intrinsic.foldSig, stringCat,
          stringCatSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addBinary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
    · have hbase : stringCatTypeAxiom.wfIn (Intrinsic.sigOf [stringCat]) := by
        simp [stringCatTypeAxiom, stringCatTerm, Intrinsic.sigOf, Intrinsic.foldSig, stringCat,
          stringCatSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnPred.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addBinary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [stringCat, List.mem_cons, List.not_mem_nil, or_false] at hφ
    have hcat : ρ.respects (some stringCatSym) := hdeps stringCat (by simp)
    simp only [Env.respects] at hcat
    have hb : ∀ x y : Runtime.Val,
        ((ρ.updateConst .value "a" x).updateConst .value "b" y).binary
          .value .value .value "string_cat" = fun a b => stringCatSym.interp (a, b) := by
      intro x y; rw [Env.updateConst_binary, Env.updateConst_binary]; simpa [stringCatSym] using hcat
    rcases hφ with rfl | rfl
    · simp only [stringCatDefAxiom, Formula.eval]
      intro x y
      simp [stringCatTerm, Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb x y, stringCatSym, valStr]
      rfl
    · simp only [stringCatTypeAxiom, Formula.eval]
      intro x y
      simp [stringCatTerm, Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb x y, stringCatSym, valStr]
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono stringCat_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars stringCat.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [stringCat_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.string, TinyML.Typ.string] ∗ _ ⊢ _
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
      ihave Hv1eq := (TinyML.ValHasType.string Θ v1).1 $$ Hv1
      ipure Hv1eq
      ihave Hv2eq := (TinyML.ValHasType.string Θ v2).1 $$ Hv2
      ipure Hv2eq
      obtain ⟨x, rfl⟩ := Hv1eq
      obtain ⟨y, rfl⟩ := Hv2eq
      rw [stringCat_toWp]
      iexists x
      iexists y
      isplitr [Hpred]
      · ipure_intro; exact ⟨rfl, rfl⟩
      · refine (assert_ret_apply Θ _ "ret" _ _ (.str (x ++ y)) ?_).trans ?_
        · exact stringCat_assert_eval ρ x y hρ
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.string_intro Θ (x ++ y)

/-- `String.equal`: byte-string equality. -/
def stringEqual : Intrinsic where
  arity    := .two
  name     := "string_equal"
  path     := some ("String", ["equal"])
  reduce   := fun (a, b) v => ∃ x y : List UInt8, a = .str x ∧ b = .str y ∧ v = .bool (x == y)
  wp       := fun (a, b) Q => iprop(∃ x y : List UInt8, ⌜a = .str x ∧ b = .str y⌝ ∗ Q (.bool (x == y)))
  spec     :=
    { args  := [("a", .string), ("b", .string)]
      retTy := .bool
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (stringEqualTerm (.var .value "a") (.var .value "b")))
          (.ret ())) }
  folSym   := some stringEqualSym
  axioms   := [stringEqualDefAxiom, stringEqualTypeAxiom]

@[simp] theorem stringEqual_arity : stringEqual.arity = .two := rfl
@[simp] theorem stringEqual_folSym : stringEqual.folSym = some stringEqualSym := rfl
@[simp] theorem stringEqual_toWp (a b : Runtime.Val) (Q : Runtime.Val → iProp) :
    stringEqual.toWp [a, b] Q =
      iprop(∃ x y : List UInt8, ⌜a = .str x ∧ b = .str y⌝ ∗ Q (.bool (x == y))) :=
  Intrinsic.toWp_two_of_arity _ _ _ _ _ _ _ _ _ Q

private theorem stringEqual_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [stringEqual]).declVars (Spec.argVars stringEqual.specArgs)) stringEqual.spec.pred := by
  apply PredTrans.checkWf_ok
  rfl

private theorem stringEqual_assert_eval (ρ : VerifM.Env) (x y : List UInt8)
    (hρ : ρ.env.respects (some stringEqualSym)) :
    (Formula.eq .value (.var .value "ret")
      (stringEqualTerm (.var .value "a") (.var .value "b"))).eval
      ((Spec.argsEnv ρ stringEqual.specArgs [.str x, .str y]).updateConst
        .value "ret" (.bool (x == y))).env := by
  have hargs := respects_argsEnv_two stringEqual.specArgs [.str x, .str y] hρ
  have hbin : (Spec.argsEnv ρ stringEqual.specArgs [.str x, .str y]).env.binary
      .value .value .value "string_equal" = fun a b => stringEqualSym.interp (a, b) := by
    simpa [Env.respects, stringEqualSym] using hargs
  show Runtime.Val.bool (x == y) =
    (Spec.argsEnv ρ stringEqual.specArgs [.str x, .str y]).env.binary
      .value .value .value "string_equal" (.str x) (.str y)
  simp [hbin, stringEqualSym]

instance : IntrinsicSound [stringEqual] stringEqual where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [stringEqual, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · have hbase : stringEqualDefAxiom.wfIn (Intrinsic.sigOf [stringEqual]) := by
        simp [stringEqualDefAxiom, stringEqualTerm, Intrinsic.sigOf, Intrinsic.foldSig,
          stringEqual, stringEqualSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addBinary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
    · have hbase : stringEqualTypeAxiom.wfIn (Intrinsic.sigOf [stringEqual]) := by
        simp [stringEqualTypeAxiom, stringEqualTerm, Intrinsic.sigOf, Intrinsic.foldSig,
          stringEqual, stringEqualSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnPred.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addBinary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [stringEqual, List.mem_cons, List.not_mem_nil, or_false] at hφ
    have heq : ρ.respects (some stringEqualSym) := hdeps stringEqual (by simp)
    simp only [Env.respects] at heq
    have hb : ∀ x y : Runtime.Val,
        ((ρ.updateConst .value "a" x).updateConst .value "b" y).binary
          .value .value .value "string_equal" = fun a b => stringEqualSym.interp (a, b) := by
      intro x y; rw [Env.updateConst_binary, Env.updateConst_binary]; simpa [stringEqualSym] using heq
    rcases hφ with rfl | rfl
    · simp only [stringEqualDefAxiom, Formula.eval]
      intro x y
      simp [stringEqualTerm, Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb x y, stringEqualSym, valStr,
        Bool.beq_eq_decide_eq]
      rfl
    · simp only [stringEqualTypeAxiom, Formula.eval]
      intro x y
      simp [stringEqualTerm, Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb x y, stringEqualSym, valStr]
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono stringEqual_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars stringEqual.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [stringEqual_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.string, TinyML.Typ.string] ∗ _ ⊢ _
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
      ihave Hv1eq := (TinyML.ValHasType.string Θ v1).1 $$ Hv1
      ipure Hv1eq
      ihave Hv2eq := (TinyML.ValHasType.string Θ v2).1 $$ Hv2
      ipure Hv2eq
      obtain ⟨x, rfl⟩ := Hv1eq
      obtain ⟨y, rfl⟩ := Hv2eq
      rw [stringEqual_toWp]
      iexists x
      iexists y
      isplitr [Hpred]
      · ipure_intro; exact ⟨rfl, rfl⟩
      · refine (assert_ret_apply Θ _ "ret" _ _ (.bool (x == y)) ?_).trans ?_
        · exact stringEqual_assert_eval ρ x y hρ
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.bool_intro Θ (x == y)

/-- `String.starts_with`: byte-string prefix test. -/
def stringStartsWith : Intrinsic where
  arity    := .two
  name     := "string_starts_with"
  path     := some ("String", ["starts_with"])
  reduce   := fun (p, s) v => ∃ x y : List UInt8, p = .str x ∧ s = .str y ∧ v = .bool (x.isPrefixOf y)
  wp       := fun (p, s) Q => iprop(∃ x y : List UInt8, ⌜p = .str x ∧ s = .str y⌝ ∗ Q (.bool (x.isPrefixOf y)))
  spec     :=
    { args  := [("prefix", .string), ("s", .string)]
      retTy := .bool
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (stringStartsWithTerm (.var .value "prefix") (.var .value "s")))
          (.ret ())) }
  folSym   := some stringStartsWithSym
  axioms   := [stringStartsWithDefAxiom, stringStartsWithTypeAxiom]

@[simp] theorem stringStartsWith_arity : stringStartsWith.arity = .two := rfl
@[simp] theorem stringStartsWith_folSym : stringStartsWith.folSym = some stringStartsWithSym := rfl
@[simp] theorem stringStartsWith_toWp (a b : Runtime.Val) (Q : Runtime.Val → iProp) :
    stringStartsWith.toWp [a, b] Q =
      iprop(∃ x y : List UInt8, ⌜a = .str x ∧ b = .str y⌝ ∗ Q (.bool (x.isPrefixOf y))) :=
  Intrinsic.toWp_two_of_arity _ _ _ _ _ _ _ _ _ Q

private theorem stringStartsWith_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [stringStartsWith]).declVars (Spec.argVars stringStartsWith.specArgs)) stringStartsWith.spec.pred := by
  apply PredTrans.checkWf_ok
  rfl

private theorem stringStartsWith_assert_eval (ρ : VerifM.Env) (x y : List UInt8)
    (hρ : ρ.env.respects (some stringStartsWithSym)) :
    (Formula.eq .value (.var .value "ret")
      (stringStartsWithTerm (.var .value "prefix") (.var .value "s"))).eval
      ((Spec.argsEnv ρ stringStartsWith.specArgs [.str x, .str y]).updateConst
        .value "ret" (.bool (x.isPrefixOf y))).env := by
  have hargs := respects_argsEnv_two stringStartsWith.specArgs [.str x, .str y] hρ
  have hbin : (Spec.argsEnv ρ stringStartsWith.specArgs [.str x, .str y]).env.binary
      .value .value .value "string_starts_with" = fun a b => stringStartsWithSym.interp (a, b) := by
    simpa [Env.respects, stringStartsWithSym] using hargs
  show Runtime.Val.bool (x.isPrefixOf y) =
    (Spec.argsEnv ρ stringStartsWith.specArgs [.str x, .str y]).env.binary
      .value .value .value "string_starts_with" (.str x) (.str y)
  simp [hbin, stringStartsWithSym]

instance : IntrinsicSound [stringStartsWith] stringStartsWith where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [stringStartsWith, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · have hbase : stringStartsWithDefAxiom.wfIn (Intrinsic.sigOf [stringStartsWith]) := by
        simp [stringStartsWithDefAxiom, stringStartsWithTerm, Intrinsic.sigOf, Intrinsic.foldSig,
          stringStartsWith, stringStartsWithSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addBinary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
    · have hbase : stringStartsWithTypeAxiom.wfIn (Intrinsic.sigOf [stringStartsWith]) := by
        simp [stringStartsWithTypeAxiom, stringStartsWithTerm, Intrinsic.sigOf, Intrinsic.foldSig,
          stringStartsWith, stringStartsWithSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnPred.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addBinary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [stringStartsWith, List.mem_cons, List.not_mem_nil, or_false] at hφ
    have hp : ρ.respects (some stringStartsWithSym) := hdeps stringStartsWith (by simp)
    simp only [Env.respects] at hp
    have hb : ∀ x y : Runtime.Val,
        ((ρ.updateConst .value "prefix" x).updateConst .value "s" y).binary
          .value .value .value "string_starts_with" = fun a b => stringStartsWithSym.interp (a, b) := by
      intro x y; rw [Env.updateConst_binary, Env.updateConst_binary]; simpa [stringStartsWithSym] using hp
    rcases hφ with rfl | rfl
    · simp only [stringStartsWithDefAxiom, Formula.eval]
      intro x y
      simp [stringStartsWithTerm, Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "prefix" ≠ "s" by decide), hb x y, stringStartsWithSym, valStr]
      rfl
    · simp only [stringStartsWithTypeAxiom, Formula.eval]
      intro x y
      simp [stringStartsWithTerm, Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "prefix" ≠ "s" by decide), hb x y, stringStartsWithSym, valStr]
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono stringStartsWith_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars stringStartsWith.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [stringStartsWith_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.string, TinyML.Typ.string] ∗ _ ⊢ _
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
      ihave Hv1eq := (TinyML.ValHasType.string Θ v1).1 $$ Hv1
      ipure Hv1eq
      ihave Hv2eq := (TinyML.ValHasType.string Θ v2).1 $$ Hv2
      ipure Hv2eq
      obtain ⟨x, rfl⟩ := Hv1eq
      obtain ⟨y, rfl⟩ := Hv2eq
      rw [stringStartsWith_toWp]
      iexists x
      iexists y
      isplitr [Hpred]
      · ipure_intro; exact ⟨rfl, rfl⟩
      · refine (assert_ret_apply Θ _ "ret" _ _ (.bool (x.isPrefixOf y)) ?_).trans ?_
        · exact stringStartsWith_assert_eval ρ x y hρ
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.bool_intro Θ (x.isPrefixOf y)

/-- `String.ends_with`: byte-string suffix test. -/
def stringEndsWith : Intrinsic where
  arity    := .two
  name     := "string_ends_with"
  path     := some ("String", ["ends_with"])
  reduce   := fun (q, s) v => ∃ x y : List UInt8, q = .str x ∧ s = .str y ∧ v = .bool (x.isSuffixOf y)
  wp       := fun (q, s) Q => iprop(∃ x y : List UInt8, ⌜q = .str x ∧ s = .str y⌝ ∗ Q (.bool (x.isSuffixOf y)))
  spec     :=
    { args  := [("suffix", .string), ("s", .string)]
      retTy := .bool
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (stringEndsWithTerm (.var .value "suffix") (.var .value "s")))
          (.ret ())) }
  folSym   := some stringEndsWithSym
  axioms   := [stringEndsWithDefAxiom, stringEndsWithTypeAxiom]

@[simp] theorem stringEndsWith_arity : stringEndsWith.arity = .two := rfl
@[simp] theorem stringEndsWith_folSym : stringEndsWith.folSym = some stringEndsWithSym := rfl
@[simp] theorem stringEndsWith_toWp (a b : Runtime.Val) (Q : Runtime.Val → iProp) :
    stringEndsWith.toWp [a, b] Q =
      iprop(∃ x y : List UInt8, ⌜a = .str x ∧ b = .str y⌝ ∗ Q (.bool (x.isSuffixOf y))) :=
  Intrinsic.toWp_two_of_arity _ _ _ _ _ _ _ _ _ Q

private theorem stringEndsWith_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [stringEndsWith]).declVars (Spec.argVars stringEndsWith.specArgs)) stringEndsWith.spec.pred := by
  apply PredTrans.checkWf_ok
  rfl

private theorem stringEndsWith_assert_eval (ρ : VerifM.Env) (x y : List UInt8)
    (hρ : ρ.env.respects (some stringEndsWithSym)) :
    (Formula.eq .value (.var .value "ret")
      (stringEndsWithTerm (.var .value "suffix") (.var .value "s"))).eval
      ((Spec.argsEnv ρ stringEndsWith.specArgs [.str x, .str y]).updateConst
        .value "ret" (.bool (x.isSuffixOf y))).env := by
  have hargs := respects_argsEnv_two stringEndsWith.specArgs [.str x, .str y] hρ
  have hbin : (Spec.argsEnv ρ stringEndsWith.specArgs [.str x, .str y]).env.binary
      .value .value .value "string_ends_with" = fun a b => stringEndsWithSym.interp (a, b) := by
    simpa [Env.respects, stringEndsWithSym] using hargs
  show Runtime.Val.bool (x.isSuffixOf y) =
    (Spec.argsEnv ρ stringEndsWith.specArgs [.str x, .str y]).env.binary
      .value .value .value "string_ends_with" (.str x) (.str y)
  simp [hbin, stringEndsWithSym]

instance : IntrinsicSound [stringEndsWith] stringEndsWith where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [stringEndsWith, List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl
    · have hbase : stringEndsWithDefAxiom.wfIn (Intrinsic.sigOf [stringEndsWith]) := by
        simp [stringEndsWithDefAxiom, stringEndsWithTerm, Intrinsic.sigOf, Intrinsic.foldSig,
          stringEndsWith, stringEndsWithSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addBinary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
    · have hbase : stringEndsWithTypeAxiom.wfIn (Intrinsic.sigOf [stringEndsWith]) := by
        simp [stringEndsWithTypeAxiom, stringEndsWithTerm, Intrinsic.sigOf, Intrinsic.foldSig,
          stringEndsWith, stringEndsWithSym, Formula.wfIn, Term.wfIn, BinOp.wfIn, UnPred.wfIn,
          Signature.extendWithSym, Signature.empty, Signature.addBinary,
          Signature.declVar, Signature.addVar, Signature.remove]
      exact Formula.wfIn_mono _ hbase hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [stringEndsWith, List.mem_cons, List.not_mem_nil, or_false] at hφ
    have hp : ρ.respects (some stringEndsWithSym) := hdeps stringEndsWith (by simp)
    simp only [Env.respects] at hp
    have hb : ∀ x y : Runtime.Val,
        ((ρ.updateConst .value "suffix" x).updateConst .value "s" y).binary
          .value .value .value "string_ends_with" = fun a b => stringEndsWithSym.interp (a, b) := by
      intro x y; rw [Env.updateConst_binary, Env.updateConst_binary]; simpa [stringEndsWithSym] using hp
    rcases hφ with rfl | rfl
    · simp only [stringEndsWithDefAxiom, Formula.eval]
      intro x y
      simp [stringEndsWithTerm, Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "suffix" ≠ "s" by decide), hb x y, stringEndsWithSym, valStr]
      rfl
    · simp only [stringEndsWithTypeAxiom, Formula.eval]
      intro x y
      simp [stringEndsWithTerm, Term.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "suffix" ≠ "s" by decide), hb x y, stringEndsWithSym, valStr]
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono stringEndsWith_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars stringEndsWith.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [stringEndsWith_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.string, TinyML.Typ.string] ∗ _ ⊢ _
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
      ihave Hv1eq := (TinyML.ValHasType.string Θ v1).1 $$ Hv1
      ipure Hv1eq
      ihave Hv2eq := (TinyML.ValHasType.string Θ v2).1 $$ Hv2
      ipure Hv2eq
      obtain ⟨x, rfl⟩ := Hv1eq
      obtain ⟨y, rfl⟩ := Hv2eq
      rw [stringEndsWith_toWp]
      iexists x
      iexists y
      isplitr [Hpred]
      · ipure_intro; exact ⟨rfl, rfl⟩
      · refine (assert_ret_apply Θ _ "ret" _ _ (.bool (x.isSuffixOf y)) ?_).trans ?_
        · exact stringEndsWith_assert_eval ρ x y hρ
        · iintro Hwand
          iapply Hwand
          exact TinyML.ValHasType.bool_intro Θ (x.isSuffixOf y)

end Intrinsics
end Stdlib

-- SUMMARY: Integer-arithmetic intrinsics (`Int.min`, `Int.max`) and their soundness instances.
import Mica.Verifier.Intrinsic

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## FOL symbols and their defining axioms

`Int.min` / `Int.max` are uninterpreted binary FOL function symbols at the
value sort. Their standard interpretation is Lean's `min` / `max` on the
integer projection of the value (matching FOL's `toInt`, which sends
non-integer values to `0`), so the interpretation is *total*: it agrees with
the defining axiom for every value, not only the integer ones. -/

/-- Integer projection of a runtime value, matching FOL's `toInt`. -/
private def valInt : Runtime.Val → Int
  | .int n => n
  | _      => 0

@[simp] private theorem valInt_int (n : Int) : valInt (.int n) = n := rfl

@[simp] private theorem toInt_eq_valInt (ρ : Env) (v : Runtime.Val) :
    UnOp.eval ρ .toInt v = valInt v := rfl

/-- FOL symbol for `Int.min`. -/
def intMinSym : FOL.Symbol .two where
  name   := "int_min"
  interp := fun (a, b) => .int (min (valInt a) (valInt b))

/-- FOL symbol for `Int.max`. -/
def intMaxSym : FOL.Symbol .two where
  name   := "int_max"
  interp := fun (a, b) => .int (max (valInt a) (valInt b))

@[simp] theorem intMinSym_name : intMinSym.name = "int_min" := rfl
@[simp] theorem intMaxSym_name : intMaxSym.name = "int_max" := rfl

private def intMinTerm (x y : Term .value) : Term .value :=
  .binop (.uninterpreted intMinSym.name .value .value .value) x y

private def intMaxTerm (x y : Term .value) : Term .value :=
  .binop (.uninterpreted intMaxSym.name .value .value .value) x y

/-- Defining axiom for `Int.min`: `toInt (int_min x y) = ite (x ≤ y) x y`,
    stated over the integer projection so it constrains all values. -/
def intMinDefAxiom : Formula :=
  .all "x" .value <| .forall_ "y" .value
    [.term (intMinTerm (.var .value "x") (.var .value "y"))] <|
    .eq .int
      (.unop .toInt (intMinTerm (.var .value "x") (.var .value "y")))
      (.ite (.binop .ge (.unop .toInt (.var .value "y")) (.unop .toInt (.var .value "x")))
            (.unop .toInt (.var .value "x"))
            (.unop .toInt (.var .value "y")))

/-- Defining axiom for `Int.max`: `toInt (int_max x y) = ite (x ≥ y) x y`. -/
def intMaxDefAxiom : Formula :=
  .all "x" .value <| .forall_ "y" .value
    [.term (intMaxTerm (.var .value "x") (.var .value "y"))] <|
    .eq .int
      (.unop .toInt (intMaxTerm (.var .value "x") (.var .value "y")))
      (.ite (.binop .ge (.unop .toInt (.var .value "x")) (.unop .toInt (.var .value "y")))
            (.unop .toInt (.var .value "x"))
            (.unop .toInt (.var .value "y")))

/-! ## Generic helpers shared by both intrinsics -/

/-- Evaluating a binop over a symbol the environment respects yields the
    symbol's standard interpretation. -/
private theorem binop_eval_respects (ρ : Env) (s : FOL.Symbol .two)
    (a b : Term .value) (hρ : ρ.respects (some s)) :
    (Term.binop (.uninterpreted s.name .value .value .value) a b).eval ρ
      = s.interp (a.eval ρ, b.eval ρ) := by
  have hbin : ρ.binary .value .value .value s.name = fun p q => s.interp (p, q) := hρ
  simp only [Term.eval, BinOp.eval, hbin]

/-- Respect for an arity-two symbol survives a `Env.updateConst` (it never
    touches the binary table). -/
private theorem respects_updateConstE {ρ : Env} {s : FOL.Symbol .two}
    {τ : Srt} {x : String} {v : τ.denote} (h : ρ.respects (some s)) :
    (ρ.updateConst τ x v).respects (some s) := by
  show (ρ.updateConst τ x v).binary .value .value .value s.name = _
  rw [Env.updateConst_binary]; exact h

/-- Respect survives the argument-binding fold. -/
private theorem respects_argsEnv {s : FOL.Symbol .two} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (name, _) :: rest, v :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine respects_argsEnv rest vs ?_
      rw [VerifM.Env.updateConst_env]; exact respects_updateConstE h

/-- Apply a `.ret (s, .assert φ ...)` spec at a value, discharging the asserted
    `φ` as a pure side condition. -/
private theorem assert_ret_apply (Θ : TinyML.TypeEnv) (Φ : Runtime.Val → iProp)
    (s : String) (ρ : VerifM.Env) (φ : Formula) (v : Runtime.Val)
    (hφ : φ.eval (ρ.updateConst .value s v).env) :
    PredTrans.apply Θ Φ (.ret (s, .assert φ (.ret ()))) ρ ⊢ Φ v := by
  simp only [PredTrans.apply, Assertion.pre, Assertion.post]
  refine (forall_elim v).trans ?_
  iintro Hw
  iapply Hw
  ipureintro
  exact hφ

/-- Shape lemma: every length-mismatched two-int argument list makes the
    typing premise inconsistent. -/
private theorem off_shape_two {Θ : TinyML.TypeEnv} {vs : List Runtime.Val}
    (P : iProp) (hlen : vs.length ≠ 2) :
    TinyML.ValsHaveTypes Θ vs [TinyML.Typ.int, TinyML.Typ.int] ⊢ P := by
  refine TinyML.ValsHaveTypes.length_eq.trans ?_
  iintro %h
  simp at h; omega

private theorem min_axiom_eval (ρ : Env)
    (hρ : ρ.binary .value .value .value "int_min"
      = fun a b => intMinSym.interp (a, b)) (x y : Runtime.Val) :
    (UnOp.eval ρ .toInt (ρ.binary .value .value .value "int_min" x y))
      = (bif BinOp.eval ρ .ge (UnOp.eval ρ .toInt y) (UnOp.eval ρ .toInt x) then
          UnOp.eval ρ .toInt x else UnOp.eval ρ .toInt y) := by
  rw [hρ]
  simp only [UnOp.eval, BinOp.eval, Bool.cond_decide]
  change valInt (intMinSym.interp (x, y)) =
    (if valInt x ≤ valInt y then valInt x else valInt y)
  by_cases h : valInt x ≤ valInt y
  · simp [intMinSym, h]
  · have hyx : valInt y ≤ valInt x := by omega
    simp [intMinSym, h, min_eq_right hyx]

private theorem max_axiom_eval (ρ : Env)
    (hρ : ρ.binary .value .value .value "int_max"
      = fun a b => intMaxSym.interp (a, b)) (x y : Runtime.Val) :
    (UnOp.eval ρ .toInt (ρ.binary .value .value .value "int_max" x y))
      = (bif BinOp.eval ρ .ge (UnOp.eval ρ .toInt x) (UnOp.eval ρ .toInt y) then
          UnOp.eval ρ .toInt x else UnOp.eval ρ .toInt y) := by
  rw [hρ]
  simp only [UnOp.eval, BinOp.eval, Bool.cond_decide]
  change valInt (intMaxSym.interp (x, y)) =
    (if valInt y ≤ valInt x then valInt x else valInt y)
  by_cases h : valInt y ≤ valInt x
  · simp [intMaxSym, h]
  · have hxy : valInt x ≤ valInt y := by omega
    simp [intMaxSym, h, max_eq_right hxy]

/-! ## `Int.min` -/

/-- `Int.min`: arity-two integer intrinsic. Its spec ties the result to the
    `int_min` FOL symbol; the defining axiom pins that symbol down for the
    solver, while the standard interpretation pins it down for the soundness
    bridge. -/
def intMin : Intrinsic where
  arity    := .two
  name     := "int_min"
  path     := some ("Int", ["min"])
  reduce   := Reduce.pure fun (a, b) v =>
    ∃ x y : Int, a = .int x ∧ b = .int y ∧ v = .int (min x y)
  wp       := fun (a, b) Q =>
    iprop(∃ x y : Int, ⌜a = .int x ∧ b = .int y⌝ ∗ Q (.int (min x y)))
  spec     :=
    { args  := [("a", .int), ("b", .int)]
      retTy := .int
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (intMinTerm (.var .value ("a")) (.var .value ("b"))))
          (.ret ())) }
  folSym   := some intMinSym
  axioms   := [intMinDefAxiom]

@[simp] theorem intMin_folSym : intMin.folSym = some intMinSym := rfl
@[simp] theorem intMin_arity : intMin.arity = .two := rfl

@[simp] theorem intMin_toWp (a b : Runtime.Val) (Q : Runtime.Val → iProp) :
    intMin.toWp [a, b] Q =
      iprop(∃ x y : Int, ⌜a = .int x ∧ b = .int y⌝ ∗ Q (.int (min x y))) :=
  Intrinsic.toWp_two_of_arity _ _ _ _ _ _ _ _ _ _

private theorem intMin_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [intMin]).declVars (Spec.argVars intMin.specArgs)) intMin.spec.pred := by
  apply PredTrans.checkWf_ok
  rfl

private theorem intMin_assert_eval (ρ : VerifM.Env) (x y : Int)
    (hρ : ρ.env.respects (some intMinSym)) :
    (Formula.eq .value (.var .value "ret")
      (intMinTerm (.var .value ("a")) (.var .value ("b")))).eval
      ((Spec.argsEnv ρ intMin.specArgs [.int x, .int y]).updateConst
        .value "ret" (.int (min x y))).env := by
  have hargs := respects_argsEnv intMin.specArgs [.int x, .int y] hρ
  have hbin : (Spec.argsEnv ρ intMin.specArgs [.int x, .int y]).env.binary
      .value .value .value "int_min" = fun a b => intMinSym.interp (a, b) := by
    simpa [Env.respects, intMinSym] using hargs
  show Runtime.Val.int (min x y) =
    (Spec.argsEnv ρ intMin.specArgs [.int x, .int y]).env.binary
      .value .value .value "int_min" (.int x) (.int y)
  simp [hbin, intMinSym]

instance : IntrinsicSound [intMin] intMin where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [intMin, List.mem_singleton] at hφ
    subst hφ
    have hbase : intMinDefAxiom.wfIn (Intrinsic.sigOf [intMin]) := by
      simp [intMinDefAxiom, intMinTerm, Intrinsic.sigOf, Intrinsic.foldSig, intMin, intMinSym,
        Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn, Signature.extendWithSym,
        Signature.empty, Signature.addBinary, Signature.declVar, Signature.addVar,
        Signature.remove]
    exact Formula.wfIn_mono intMinDefAxiom hbase hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [intMin, List.mem_singleton] at hφ
    subst hφ
    have hmin : ρ.respects (some intMinSym) := hdeps intMin (by simp)
    simp only [Env.respects] at hmin
    simp only [intMinDefAxiom, Formula.all, Formula.eval]
    intro x y
    have hb : ((ρ.updateConst .value "x" x).updateConst .value "y" y).binary
        .value .value .value "int_min" = fun a b => intMinSym.interp (a, b) := by
      rw [Env.updateConst_binary, Env.updateConst_binary]
      simpa [intMinSym] using hmin
    simpa [intMinTerm, Term.eval, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "x" ≠ "y" by decide)] using
      min_axiom_eval (((ρ.updateConst .value "x" x).updateConst .value "y" y)) hb x y
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono intMin_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars intMin.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [intMin_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.int, TinyML.Typ.int] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_left (off_shape_two _ (by simp))).trans sep_elim_left
    | [_] => exact (sep_mono_left (off_shape_two _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ :: _ => exact (sep_mono_left (off_shape_two _ (by simp))).trans sep_elim_left
    | [v1, v2] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v1 [v2] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv1, Hvs2⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ v2 [] _ _).1 $$ Hvs2
      icases Hcons2 with ⟨Hv2, _⟩
      ihave Hv1eq := (TinyML.ValHasType.int Θ v1).1 $$ Hv1
      ipure Hv1eq
      ihave Hv2eq := (TinyML.ValHasType.int Θ v2).1 $$ Hv2
      ipure Hv2eq
      obtain ⟨x, rfl⟩ := Hv1eq
      obtain ⟨y, rfl⟩ := Hv2eq
      rw [intMin_toWp]
      iexists x
      iexists y
      isplitr [Hpred]
      · ipureintro; exact ⟨rfl, rfl⟩
      · refine (assert_ret_apply Θ _ "ret" _ _ (.int (min x y)) ?_).trans ?_
        · exact intMin_assert_eval ρ x y hρ
        · iintro Hwand
          iapply Hwand
          change ⊢ TinyML.ValHasType Θ (.int (min x y)) TinyML.Typ.int
          exact TinyML.ValHasType.int_intro Θ (min x y)

/-! ## `Int.max` -/

/-- `Int.max`: arity-two integer intrinsic, mirroring `Int.min`. -/
def intMax : Intrinsic where
  arity    := .two
  name     := "int_max"
  path     := some ("Int", ["max"])
  reduce   := Reduce.pure fun (a, b) v =>
    ∃ x y : Int, a = .int x ∧ b = .int y ∧ v = .int (max x y)
  wp       := fun (a, b) Q =>
    iprop(∃ x y : Int, ⌜a = .int x ∧ b = .int y⌝ ∗ Q (.int (max x y)))
  spec     :=
    { args  := [("a", .int), ("b", .int)]
      retTy := .int
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (intMaxTerm (.var .value ("a")) (.var .value ("b"))))
          (.ret ())) }
  folSym   := some intMaxSym
  axioms   := [intMaxDefAxiom]

@[simp] theorem intMax_folSym : intMax.folSym = some intMaxSym := rfl
@[simp] theorem intMax_arity : intMax.arity = .two := rfl

@[simp] theorem intMax_toWp (a b : Runtime.Val) (Q : Runtime.Val → iProp) :
    intMax.toWp [a, b] Q =
      iprop(∃ x y : Int, ⌜a = .int x ∧ b = .int y⌝ ∗ Q (.int (max x y))) :=
  Intrinsic.toWp_two_of_arity _ _ _ _ _ _ _ _ _ _

private theorem intMax_base_wf :
    PredTrans.wfIn
      ((Intrinsic.sigOf [intMax]).declVars (Spec.argVars intMax.specArgs)) intMax.spec.pred := by
  apply PredTrans.checkWf_ok
  rfl

private theorem intMax_assert_eval (ρ : VerifM.Env) (x y : Int)
    (hρ : ρ.env.respects (some intMaxSym)) :
    (Formula.eq .value (.var .value "ret")
      (intMaxTerm (.var .value ("a")) (.var .value ("b")))).eval
      ((Spec.argsEnv ρ intMax.specArgs [.int x, .int y]).updateConst
        .value "ret" (.int (max x y))).env := by
  have hargs := respects_argsEnv intMax.specArgs [.int x, .int y] hρ
  have hbin : (Spec.argsEnv ρ intMax.specArgs [.int x, .int y]).env.binary
      .value .value .value "int_max" = fun a b => intMaxSym.interp (a, b) := by
    simpa [Env.respects, intMaxSym] using hargs
  show Runtime.Val.int (max x y) =
    (Spec.argsEnv ρ intMax.specArgs [.int x, .int y]).env.binary
      .value .value .value "int_max" (.int x) (.int y)
  simp [hbin, intMaxSym]

instance : IntrinsicSound [intMax] intMax where
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [intMax, List.mem_singleton] at hφ
    subst hφ
    have hbase : intMaxDefAxiom.wfIn (Intrinsic.sigOf [intMax]) := by
      simp [intMaxDefAxiom, intMaxTerm, Intrinsic.sigOf, Intrinsic.foldSig, intMax, intMaxSym,
        Formula.wfIn, Term.wfIn, BinOp.wfIn, UnOp.wfIn,
        Signature.extendWithSym, Signature.empty, Signature.addBinary,
        Signature.declVar, Signature.addVar, Signature.remove]
    exact Formula.wfIn_mono intMaxDefAxiom hbase hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [intMax, List.mem_singleton] at hφ
    subst hφ
    have hmax : ρ.respects (some intMaxSym) := hdeps intMax (by simp)
    simp only [Env.respects] at hmax
    simp only [intMaxDefAxiom, Formula.all, Formula.eval]
    intro x y
    have hb : ((ρ.updateConst .value "x" x).updateConst .value "y" y).binary
        .value .value .value "int_max" = fun a b => intMaxSym.interp (a, b) := by
      rw [Env.updateConst_binary, Env.updateConst_binary]
      simpa [intMaxSym] using hmax
    simpa [intMaxTerm, Term.eval, Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "x" ≠ "y" by decide)] using
      max_axiom_eval (((ρ.updateConst .value "x" x).updateConst .value "y" y)) hb x y
  specWf := by
    intro Δ hsub hwf
    exact PredTrans.wfIn_mono intMax_base_wf
      (Signature.Subset.declVars hsub (Spec.argVars intMax.specArgs))
      (Signature.wf_declVars hwf)
  bridge := by
    intro Θ vs ρ Φ hρ
    simp only [intMax_folSym, Env.respects] at hρ
    show TinyML.ValsHaveTypes Θ vs [TinyML.Typ.int, TinyML.Typ.int] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_left (off_shape_two _ (by simp))).trans sep_elim_left
    | [_] => exact (sep_mono_left (off_shape_two _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ :: _ => exact (sep_mono_left (off_shape_two _ (by simp))).trans sep_elim_left
    | [v1, v2] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v1 [v2] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv1, Hvs2⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ v2 [] _ _).1 $$ Hvs2
      icases Hcons2 with ⟨Hv2, _⟩
      ihave Hv1eq := (TinyML.ValHasType.int Θ v1).1 $$ Hv1
      ipure Hv1eq
      ihave Hv2eq := (TinyML.ValHasType.int Θ v2).1 $$ Hv2
      ipure Hv2eq
      obtain ⟨x, rfl⟩ := Hv1eq
      obtain ⟨y, rfl⟩ := Hv2eq
      rw [intMax_toWp]
      iexists x
      iexists y
      isplitr [Hpred]
      · ipureintro; exact ⟨rfl, rfl⟩
      · refine (assert_ret_apply Θ _ "ret" _ _ (.int (max x y)) ?_).trans ?_
        · exact intMax_assert_eval ρ x y hρ
        · iintro Hwand
          iapply Hwand
          change ⊢ TinyML.ValHasType Θ (.int (max x y)) TinyML.Typ.int
          exact TinyML.ValHasType.int_intro Θ (max x y)

end Intrinsics
end Stdlib

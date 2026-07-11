-- SUMMARY: Immutable-vector intrinsics (`Vec.length`, `Vec.get`, `Vec.set`, `Vec.make`) and their soundness instances.
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

`get`/`set` are partial: their `reduce` relations demand an in-bounds index, so
an out-of-bounds call is stuck, and the `spec.pred` precondition is what makes
the weakest precondition provable at a call site. `make` demands a nonnegative
length.
-/

namespace Stdlib

open Verifier

namespace Intrinsics

/-- Vector projection of a runtime value, matching FOL's `toVec`. -/
def valVec : Runtime.Val → List Runtime.Val
  | .vec l => l
  | _      => []

private theorem vec_respects_argsEnv_one {s : FOL.Symbol .one} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (_, _) :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine vec_respects_argsEnv_one rest vs ?_
      rw [VerifM.Env.updateConst_env]
      simpa only [Env.respects, Env.updateConst_unary] using h

private theorem vec_respects_argsEnv_two {s : FOL.Symbol .two} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (_, _) :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine vec_respects_argsEnv_two rest vs ?_
      rw [VerifM.Env.updateConst_env]
      simpa only [Env.respects, Env.updateConst_binary] using h

private theorem vec_respects_argsEnv_three {s : FOL.Symbol .three} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (_, _) :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine vec_respects_argsEnv_three rest vs ?_
      rw [VerifM.Env.updateConst_env]
      simpa only [Env.respects, Env.updateConst_ternary] using h

/-! ## FOL symbols

Value-sorted counterparts of the `Vec`-sorted operations. Each standard
interpretation projects its arguments (`valVec`/`valInt`, matching FOL's
`toVec`/`toInt`) and injects the result. Negative indices and lengths have
explicit totalized behavior matching the interpreted FOL operations. -/

def vecLengthSym : FOL.Symbol .one where
  name   := "val_vec_length"
  interp := fun v => .int (valVec v).length

def vecGetSym : FOL.Symbol .two where
  name   := "val_vec_get"
  interp := fun (v, i) =>
    let n := valInt i
    if 0 ≤ n then ((valVec v)[n.toNat]?).getD .unit else .unit

def vecSetSym : FOL.Symbol .three where
  name   := "val_vec_set"
  interp := fun (v, i, x) =>
    let n := valInt i
    .vec (if 0 ≤ n then (valVec v).set n.toNat x else valVec v)

def vecMakeSym : FOL.Symbol .two where
  name   := "val_vec_make"
  interp := fun (n, x) =>
    let len := valInt n
    .vec (if 0 ≤ len then List.replicate len.toNat x else [])

@[simp] theorem vecLengthSym_name : vecLengthSym.name = "val_vec_length" := rfl
@[simp] theorem vecGetSym_name : vecGetSym.name = "val_vec_get" := rfl
@[simp] theorem vecSetSym_name : vecSetSym.name = "val_vec_set" := rfl
@[simp] theorem vecMakeSym_name : vecMakeSym.name = "val_vec_make" := rfl

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

def vecLengthTypeAxiom : Formula :=
  .forall_ "v" .value [.term (unTerm "val_vec_length" (.var .value "v"))] <|
    .unpred .isInt (unTerm "val_vec_length" (.var .value "v"))

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

def vecSetTypeAxiom : Formula :=
  .all "v" .value <| .all "i" .value <| .forall_ "x" .value
    [.term (terTerm "val_vec_set" (.var .value "v") (.var .value "i") (.var .value "x"))] <|
    .unpred .isVec (terTerm "val_vec_set" (.var .value "v") (.var .value "i") (.var .value "x"))

def vecMakeDefAxiom : Formula :=
  .all "n" .value <| .forall_ "x" .value
    [.term (binTerm "val_vec_make" (.var .value "n") (.var .value "x"))] <|
    .eq .value
      (binTerm "val_vec_make" (.var .value "n") (.var .value "x"))
      (.unop .ofVec (.binop .vecMake (intOf "n") (.var .value "x")))

def vecMakeTypeAxiom : Formula :=
  .all "n" .value <| .forall_ "x" .value
    [.term (binTerm "val_vec_make" (.var .value "n") (.var .value "x"))] <|
    .unpred .isVec (binTerm "val_vec_make" (.var .value "n") (.var .value "x"))

/-! ## `Vec.length` -/

/-- `Vec.length : 'a vec -> int`. Total. -/
def vecLength : Intrinsic where
  arity  := .one
  name   := "val_vec_length"
  path   := some ("Vec", ["length"])
  reduce := Reduce.pure fun v r => ∃ l, v = .vec l ∧ r = .int l.length
  wp     := fun v Q => iprop(∃ l, ⌜v = .vec l⌝ ∗ Q (.int l.length))
  spec   :=
    { args  := [("v", .vec (.tvar "a"))]
      retTy := .int
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (unTerm "val_vec_length" (.var .value "v"))) (.ret ())) }
  typing := fun _ tys =>
    match tys with
    | [.vec t] => .ok [("a", t)]
    | [_] => .error "Vec.length expects a vector argument"
    | _ => .error s!"expected 1 argument, got {tys.length}"
  folSym := some vecLengthSym
  axioms := [⟨vecLengthDefAxiom, .high⟩, ⟨vecLengthTypeAxiom, .high⟩]

@[simp] theorem vecLength_arity : vecLength.arity = .one := rfl
@[simp] theorem vecLength_folSym : vecLength.folSym = some vecLengthSym := rfl

@[simp] theorem vecLength.toWp_eq (v : Runtime.Val) (Q : Runtime.Val → iProp) :
    vecLength.toWp [v] Q = iprop(∃ l, ⌜v = .vec l⌝ ∗ Q (.int l.length)) := rfl

@[simp] theorem vecLength.toReduce_eq (v r : Runtime.Val) (μ μ' : TinyML.Heap) :
    vecLength.toReduce [v] μ r μ' =
      ((∃ l, v = .vec l ∧ r = .int l.length) ∧ μ' = μ) := rfl

@[simp] theorem vecLength.instantiate_args (σ : TinyML.TyVar → TinyML.Typ) :
    (vecLength.spec.instantiate σ).args = [("v", .vec (σ "a"))] := by
  simp [vecLength, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem vecLength.instantiate_retTy (σ : TinyML.TyVar → TinyML.Typ) :
    (vecLength.spec.instantiate σ).retTy = .int := by
  simp [vecLength, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem vecLength.spec_pred :
    vecLength.spec.pred = .ret ("ret",
      .assert (.eq .value (.var .value "ret")
        (unTerm "val_vec_length" (.var .value "v"))) (.ret ())) := rfl

instance : IntrinsicSound [vecLength] vecLength where
  specWf := fun _ hsub hwf =>
    specWf_of_base (by apply PredTrans.checkWf_ok; rfl) hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | [] => exact false_elim
    | _ :: _ :: _ => exact false_elim
    | [v] =>
      have hred : ∀ l μ r μ',
          ctx vecLength.name [.vec l] μ r μ' ↔ r = .int l.length ∧ μ' = μ := by
        intro l μ r μ'
        rw [hctx]
        simp only [vecLength.toReduce_eq]
        constructor
        · rintro ⟨⟨l', hv, hr⟩, hμ⟩
          cases hv
          exact ⟨hr, hμ⟩
        · rintro ⟨hr, hμ⟩
          exact ⟨⟨l, rfl, hr⟩, hμ⟩
      show iprop(∃ l, ⌜v = .vec l⌝ ∗ Φ (.int l.length)) ⊢ _
      istart
      iintro ⟨%l, %hv, HΦ⟩
      obtain rfl := hv
      iapply (wp.prim_pure (hred l) ⟨_, rfl⟩)
      iintro %r %hr
      subst hr
      iexact HΦ
  bridge := by
    intro _ σ Θ vs ρ Φ hρ
    simp only [vecLength.instantiate_args, vecLength.instantiate_retTy,
      Spec.instantiate_pred, vecLength.spec_pred, List.map_cons, List.map_nil]
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [v] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, _⟩
      ihave Hvec := (TinyML.ValHasType.vec Θ v (σ "a")).1 $$ Hv
      icases Hvec with ⟨%l, %hv, _⟩
      obtain rfl := hv
      simp only [vecLength.toWp_eq]
      iexists l
      isplitr [Hpred]
      · ipureintro; rfl
      · have hassert : (Formula.eq .value (.var .value "ret")
            (unTerm "val_vec_length" (.var .value "v"))).eval
            ((Spec.argsEnv ρ [("v", TinyML.Typ.vec (σ "a"))] [.vec l]).updateConst
              .value "ret" (.int l.length)).env := by
          have hargs := vec_respects_argsEnv_one
            [("v", TinyML.Typ.vec (σ "a"))] [Runtime.Val.vec l] hρ
          have hun : (Spec.argsEnv ρ [("v", TinyML.Typ.vec (σ "a"))] [.vec l]).env.unary
              .value .value "val_vec_length" = vecLengthSym.interp := by
            simpa [Env.respects, vecLengthSym] using hargs
          show Runtime.Val.int l.length =
            (Spec.argsEnv ρ [("v", TinyML.Typ.vec (σ "a"))] [.vec l]).env.unary
              .value .value "val_vec_length" (.vec l)
          rw [hun]
          simp [vecLengthSym, valVec]
        refine (assert_ret_apply Θ _ "ret" _ _ (.int l.length) hassert).trans ?_
        iintro Hwand
        iapply Hwand
        exact TinyML.ValHasType.int_intro Θ l.length
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [vecLength, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    rcases hφ with rfl | rfl
    · exact Formula.wfIn_mono _ (by apply Formula.checkWf_ok; rfl) hsub hwf
    · exact Formula.wfIn_mono _ (by apply Formula.checkWf_ok; rfl) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [vecLength, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    have hresp : ρ.respects (some vecLengthSym) := by
      have h := hdeps vecLength (by simp)
      simpa [vecLength] using h
    have hun : ∀ v : Runtime.Val,
        (ρ.updateConst .value "v" v).unary .value .value "val_vec_length" = vecLengthSym.interp := by
      intro v
      rw [Env.updateConst_unary]
      simpa [Env.respects, vecLengthSym] using hresp
    rcases hφ with rfl | rfl
    · simp only [vecLengthDefAxiom, Formula.eval]
      intro v
      simp only [unTerm, vecOf, vecLengthSym, hun v, Term.eval, UnOp.eval,
        Env.lookupConst_updateConst_same, valVec]
      rfl
    · simp only [vecLengthTypeAxiom, Formula.eval]
      intro v
      simp [unTerm, vecLengthSym, hun v, Term.eval, Env.lookupConst_updateConst_same]

/-! ## `Vec.get` -/

/-- `Vec.get : 'a vec -> int -> 'a`. Partial: the index must be in bounds. -/
def vecGet : Intrinsic where
  arity  := .two
  name   := "val_vec_get"
  path   := some ("Vec", ["get"])
  reduce := Reduce.pure fun (v, i) r =>
    ∃ l n, v = .vec l ∧ i = .int n ∧ 0 ≤ n ∧ n < (l.length : Int) ∧
      r = (l[n.toNat]?).getD .unit
  wp     := fun (v, i) Q =>
    iprop(∃ l n, ⌜v = .vec l ∧ i = .int n ∧ 0 ≤ n ∧ n < (l.length : Int)⌝ ∗
      Q ((l[n.toNat]?).getD .unit))
  spec   :=
    { args  := [("v", .vec (.tvar "a")), ("i", .int)]
      retTy := .tvar "a"
      pred  := .assert (vecBoundsPre "v" "i") <|
        .ret ("ret",
          .assert (.eq .value (.var .value "ret")
            (binTerm "val_vec_get" (.var .value "v") (.var .value "i"))) (.ret ())) }
  typing := fun _ tys =>
    match tys with
    | [.vec t, _] => .ok [("a", t)]
    | [_, _] => .error "Vec.get expects a vector as its first argument"
    | _ => .error s!"expected 2 arguments, got {tys.length}"
  folSym := some vecGetSym
  axioms := [⟨vecGetDefAxiom, .high⟩]

@[simp] theorem vecGet_arity : vecGet.arity = .two := rfl
@[simp] theorem vecGet_folSym : vecGet.folSym = some vecGetSym := rfl

@[simp] theorem vecGet.toWp_eq (v i : Runtime.Val) (Q : Runtime.Val → iProp) :
    vecGet.toWp [v, i] Q =
      iprop(∃ l n, ⌜v = .vec l ∧ i = .int n ∧ 0 ≤ n ∧ n < (l.length : Int)⌝ ∗
        Q ((l[n.toNat]?).getD .unit)) := rfl

@[simp] theorem vecGet.toReduce_eq (v i r : Runtime.Val) (μ μ' : TinyML.Heap) :
    vecGet.toReduce [v, i] μ r μ' =
      ((∃ l n, v = .vec l ∧ i = .int n ∧ 0 ≤ n ∧ n < (l.length : Int) ∧
        r = (l[n.toNat]?).getD .unit) ∧ μ' = μ) := rfl

@[simp] theorem vecGet.instantiate_args (σ : TinyML.TyVar → TinyML.Typ) :
    (vecGet.spec.instantiate σ).args = [("v", .vec (σ "a")), ("i", .int)] := by
  simp [vecGet, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem vecGet.instantiate_retTy (σ : TinyML.TyVar → TinyML.Typ) :
    (vecGet.spec.instantiate σ).retTy = σ "a" := by
  simp [vecGet, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem vecGet.spec_pred :
    vecGet.spec.pred = .assert (vecBoundsPre "v" "i")
      (.ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (binTerm "val_vec_get" (.var .value "v") (.var .value "i"))) (.ret ()))) := rfl

instance : IntrinsicSound [vecGet] vecGet where
  specWf := fun _ hsub hwf =>
    specWf_of_base (by apply PredTrans.checkWf_ok; rfl) hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | [] => exact false_elim
    | [_] => exact false_elim
    | _ :: _ :: _ :: _ => exact false_elim
    | [v, i] =>
      have hred : ∀ l n μ r μ',
          ctx vecGet.name [.vec l, .int n] μ r μ'
            ↔ (0 ≤ n ∧ n < (l.length : Int) ∧ r = (l[n.toNat]?).getD .unit) ∧ μ' = μ := by
        intro l n μ r μ'
        rw [hctx]
        simp only [vecGet.toReduce_eq]
        constructor
        · rintro ⟨⟨l', n', hv, hi, hlo, hhi, hr⟩, hμ⟩
          cases hv
          cases hi
          exact ⟨⟨hlo, hhi, hr⟩, hμ⟩
        · rintro ⟨⟨hlo, hhi, hr⟩, hμ⟩
          exact ⟨⟨l, n, rfl, rfl, hlo, hhi, hr⟩, hμ⟩
      show iprop(∃ l n, ⌜v = .vec l ∧ i = .int n ∧ 0 ≤ n ∧ n < (l.length : Int)⌝ ∗
        Φ ((l[n.toNat]?).getD .unit)) ⊢ _
      istart
      iintro ⟨%l, %n, %ha, HΦ⟩
      obtain ⟨rfl, rfl, hlo, hhi⟩ := ha
      iapply (wp.prim_pure (hred l n) ⟨_, hlo, hhi, rfl⟩)
      iintro %r %hr
      obtain ⟨_, _, rfl⟩ := hr
      iexact HΦ
  bridge := by
    intro _ σ Θ vs ρ Φ hρ
    simp only [vecGet.instantiate_args, vecGet.instantiate_retTy,
      Spec.instantiate_pred, vecGet.spec_pred, List.map_cons, List.map_nil]
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [v, i] =>
      simp only [PredTrans.apply, Assertion.pre]
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [i] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, Hrest⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ i [] _ _).1 $$ Hrest
      icases Hcons2 with ⟨Hi, _⟩
      ihave Hvec := (TinyML.ValHasType.vec Θ v (σ "a")).1 $$ Hv
      icases Hvec with ⟨%l, %hv, Helems⟩
      obtain rfl := hv
      ihave Hieq := (TinyML.ValHasType.int Θ i).1 $$ Hi
      ipure Hieq
      obtain ⟨n, rfl⟩ := Hieq
      icases Hpred with ⟨%hpre, Hpost⟩
      have hbounds : 0 ≤ n ∧ n < (l.length : Int) := by
        simpa [vecBoundsPre, vecOf, intOf, Spec.argsEnv, Formula.eval, Term.eval,
          VerifM.Env.updateConst_env, Env.lookupConst_updateConst_same,
          Env.lookupConst_updateConst_ne (show "v" ≠ "i" by decide)] using hpre
      have hlt : n.toNat < l.length := by omega
      have hget : l[n.toNat]? = some l[n.toNat] := List.getElem?_eq_getElem hlt
      simp only [vecGet.toWp_eq]
      iexists l
      iexists n
      isplitr [Hpost Helems]
      · ipureintro
        exact ⟨rfl, rfl, hbounds.1, hbounds.2⟩
      · have hassert : (Formula.eq .value (.var .value "ret")
            (binTerm "val_vec_get" (.var .value "v") (.var .value "i"))).eval
            ((Spec.argsEnv ρ [("v", TinyML.Typ.vec (σ "a")), ("i", TinyML.Typ.int)]
              [.vec l, .int n]).updateConst .value "ret" ((l[n.toNat]?).getD .unit)).env := by
          have hargs := vec_respects_argsEnv_two
            [("v", TinyML.Typ.vec (σ "a")), ("i", TinyML.Typ.int)]
            [Runtime.Val.vec l, Runtime.Val.int n] hρ
          have hbin : (Spec.argsEnv ρ [("v", TinyML.Typ.vec (σ "a")), ("i", TinyML.Typ.int)]
              [.vec l, .int n]).env.binary .value .value .value "val_vec_get"
                = fun a b => vecGetSym.interp (a, b) := by
            simpa [Env.respects, vecGetSym] using hargs
          show (l[n.toNat]?).getD .unit =
            (Spec.argsEnv ρ [("v", TinyML.Typ.vec (σ "a")), ("i", TinyML.Typ.int)]
              [.vec l, .int n]).env.binary .value .value .value "val_vec_get"
                (.vec l) (.int n)
          rw [hbin]
          simp [vecGetSym, valVec, valInt, hbounds.1]
        refine (sep_mono_right
          (assert_ret_apply Θ _ "ret" _ _ ((l[n.toNat]?).getD .unit) hassert)).trans ?_
        iintro ⟨Helems, Hwand⟩
        iapply Hwand
        simp only [hget, Option.getD_some]
        iapply (BigSepL.bigSepL_lookup
          (Φ := fun _ w => TinyML.ValHasType Θ w (σ "a")) hget)
        iexact Helems
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [vecGet, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    subst hφ
    exact Formula.wfIn_mono _ (by apply Formula.checkWf_ok; rfl) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [vecGet, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    have hresp : ρ.respects (some vecGetSym) := by
      have h := hdeps vecGet (by simp)
      simpa [vecGet] using h
    subst hφ
    simp only [vecGetDefAxiom, Formula.all, Formula.eval]
    intro v i
    have hbin : (((ρ.updateConst .value "v" v).updateConst .value "i" i).binary
        .value .value .value "val_vec_get") = fun a b => vecGetSym.interp (a, b) := by
      rw [Env.updateConst_binary, Env.updateConst_binary]
      simpa [Env.respects, vecGetSym] using hresp
    simp only [binTerm, vecOf, intOf, vecGetSym, hbin, Term.eval, UnOp.eval, BinOp.eval,
      Env.lookupConst_updateConst_same,
      Env.lookupConst_updateConst_ne (show "v" ≠ "i" by decide), valVec, valInt]
    rfl

/-! ## `Vec.set` -/

/-- `Vec.set : 'a vec -> int -> 'a -> 'a vec`, the copying functional update.
    Partial: the index must be in bounds. -/
def vecSet : Intrinsic where
  arity  := .three
  name   := "val_vec_set"
  path   := some ("Vec", ["set"])
  reduce := Reduce.pure fun (v, i, x) r =>
    ∃ l n, v = .vec l ∧ i = .int n ∧ 0 ≤ n ∧ n < (l.length : Int) ∧
      r = .vec (l.set n.toNat x)
  wp     := fun (v, i, x) Q =>
    iprop(∃ l n, ⌜v = .vec l ∧ i = .int n ∧ 0 ≤ n ∧ n < (l.length : Int)⌝ ∗
      Q (.vec (l.set n.toNat x)))
  spec   :=
    { args  := [("v", .vec (.tvar "a")), ("i", .int), ("x", .tvar "a")]
      retTy := .vec (.tvar "a")
      pred  := .assert (vecBoundsPre "v" "i") <|
        .ret ("ret",
          .assert (.eq .value (.var .value "ret")
            (terTerm "val_vec_set" (.var .value "v") (.var .value "i") (.var .value "x")))
            (.ret ())) }
  typing := fun _ tys =>
    match tys with
    | [.vec t, _, _] => .ok [("a", t)]
    | [_, _, _] => .error "Vec.set expects a vector as its first argument"
    | _ => .error s!"expected 3 arguments, got {tys.length}"
  folSym := some vecSetSym
  axioms := [⟨vecSetDefAxiom, .high⟩, ⟨vecSetTypeAxiom, .high⟩]

@[simp] theorem vecSet_arity : vecSet.arity = .three := rfl
@[simp] theorem vecSet_folSym : vecSet.folSym = some vecSetSym := rfl

@[simp] theorem vecSet.toWp_eq (v i x : Runtime.Val) (Q : Runtime.Val → iProp) :
    vecSet.toWp [v, i, x] Q =
      iprop(∃ l n, ⌜v = .vec l ∧ i = .int n ∧ 0 ≤ n ∧ n < (l.length : Int)⌝ ∗
        Q (.vec (l.set n.toNat x))) := rfl

@[simp] theorem vecSet.toReduce_eq (v i x r : Runtime.Val) (μ μ' : TinyML.Heap) :
    vecSet.toReduce [v, i, x] μ r μ' =
      ((∃ l n, v = .vec l ∧ i = .int n ∧ 0 ≤ n ∧ n < (l.length : Int) ∧
        r = .vec (l.set n.toNat x)) ∧ μ' = μ) := rfl

@[simp] theorem vecSet.instantiate_args (σ : TinyML.TyVar → TinyML.Typ) :
    (vecSet.spec.instantiate σ).args
      = [("v", .vec (σ "a")), ("i", .int), ("x", σ "a")] := by
  simp [vecSet, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem vecSet.instantiate_retTy (σ : TinyML.TyVar → TinyML.Typ) :
    (vecSet.spec.instantiate σ).retTy = .vec (σ "a") := by
  simp [vecSet, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem vecSet.spec_pred :
    vecSet.spec.pred = .assert (vecBoundsPre "v" "i")
      (.ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (terTerm "val_vec_set" (.var .value "v") (.var .value "i") (.var .value "x")))
          (.ret ()))) := rfl

instance : IntrinsicSound [vecSet] vecSet where
  specWf := fun _ hsub hwf =>
    specWf_of_base (by apply PredTrans.checkWf_ok; rfl) hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | [] => exact false_elim
    | [_] => exact false_elim
    | [_, _] => exact false_elim
    | _ :: _ :: _ :: _ :: _ => exact false_elim
    | [v, i, x] =>
      have hred : ∀ l n μ r μ',
          ctx vecSet.name [.vec l, .int n, x] μ r μ'
            ↔ (0 ≤ n ∧ n < (l.length : Int) ∧ r = .vec (l.set n.toNat x)) ∧ μ' = μ := by
        intro l n μ r μ'
        rw [hctx]
        simp only [vecSet.toReduce_eq]
        constructor
        · rintro ⟨⟨l', n', hv, hi, hlo, hhi, hr⟩, hμ⟩
          cases hv
          cases hi
          exact ⟨⟨hlo, hhi, hr⟩, hμ⟩
        · rintro ⟨⟨hlo, hhi, hr⟩, hμ⟩
          exact ⟨⟨l, n, rfl, rfl, hlo, hhi, hr⟩, hμ⟩
      show iprop(∃ l n, ⌜v = .vec l ∧ i = .int n ∧ 0 ≤ n ∧ n < (l.length : Int)⌝ ∗
        Φ (.vec (l.set n.toNat x))) ⊢ _
      istart
      iintro ⟨%l, %n, %ha, HΦ⟩
      obtain ⟨rfl, rfl, hlo, hhi⟩ := ha
      iapply (wp.prim_pure (hred l n) ⟨_, hlo, hhi, rfl⟩)
      iintro %r %hr
      obtain ⟨_, _, rfl⟩ := hr
      iexact HΦ
  bridge := by
    intro _ σ Θ vs ρ Φ hρ
    simp only [vecSet.instantiate_args, vecSet.instantiate_retTy,
      Spec.instantiate_pred, vecSet.spec_pred, List.map_cons, List.map_nil]
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_, _] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [v, i, x] =>
      simp only [PredTrans.apply, Assertion.pre]
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [i, x] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, Hrest⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ i [x] _ _).1 $$ Hrest
      icases Hcons2 with ⟨Hi, Hrest2⟩
      ihave Hcons3 := (TinyML.ValsHaveTypes.cons Θ x [] _ _).1 $$ Hrest2
      icases Hcons3 with ⟨Hx, _⟩
      ihave Hvec := (TinyML.ValHasType.vec Θ v (σ "a")).1 $$ Hv
      icases Hvec with ⟨%l, %hv, Helems⟩
      obtain rfl := hv
      ihave Hieq := (TinyML.ValHasType.int Θ i).1 $$ Hi
      ipure Hieq
      obtain ⟨n, rfl⟩ := Hieq
      icases Hpred with ⟨%hpre, Hpost⟩
      have hbounds : 0 ≤ n ∧ n < (l.length : Int) := by
        simpa [vecBoundsPre, vecOf, intOf, Spec.argsEnv, Formula.eval, Term.eval,
          VerifM.Env.updateConst_env, Env.lookupConst_updateConst_same,
          Env.lookupConst_updateConst_ne (show "v" ≠ "i" by decide),
          Env.lookupConst_updateConst_ne (show "v" ≠ "x" by decide),
          Env.lookupConst_updateConst_ne (show "i" ≠ "x" by decide)] using hpre
      have hlt : n.toNat < l.length := by omega
      have hget : l[n.toNat]? = some l[n.toNat] := List.getElem?_eq_getElem hlt
      ihave Hty : iprop(TinyML.ValHasType Θ (Runtime.Val.vec (l.set n.toNat x))
          ((σ "a").vec)) $$ [Helems Hx]
      · iapply (TinyML.ValHasType.vec_set Θ hget)
        isplitl [Helems]
        · iexact Helems
        · iexact Hx
      simp only [vecSet.toWp_eq]
      iexists l
      iexists n
      isplitr [Hpost Hty]
      · ipureintro
        exact ⟨rfl, rfl, hbounds.1, hbounds.2⟩
      · have hassert : (Formula.eq .value (.var .value "ret")
            (terTerm "val_vec_set" (.var .value "v") (.var .value "i") (.var .value "x"))).eval
            ((Spec.argsEnv ρ [("v", TinyML.Typ.vec (σ "a")), ("i", TinyML.Typ.int),
                ("x", σ "a")] [.vec l, .int n, x]).updateConst
              .value "ret" (.vec (l.set n.toNat x))).env := by
          have hargs := vec_respects_argsEnv_three
            [("v", TinyML.Typ.vec (σ "a")), ("i", TinyML.Typ.int), ("x", σ "a")]
            [Runtime.Val.vec l, Runtime.Val.int n, x] hρ
          have hter : (Spec.argsEnv ρ [("v", TinyML.Typ.vec (σ "a")), ("i", TinyML.Typ.int),
              ("x", σ "a")] [.vec l, .int n, x]).env.ternary
                .value .value .value .value "val_vec_set"
                = fun a b c => vecSetSym.interp (a, b, c) := by
            simpa [Env.respects, vecSetSym] using hargs
          show Runtime.Val.vec (l.set n.toNat x) =
            (Spec.argsEnv ρ [("v", TinyML.Typ.vec (σ "a")), ("i", TinyML.Typ.int),
              ("x", σ "a")] [.vec l, .int n, x]).env.ternary
                .value .value .value .value "val_vec_set" (.vec l) (.int n) x
          rw [hter]
          simp [vecSetSym, valVec, valInt, hbounds.1]
        refine (sep_mono_left
          (assert_ret_apply Θ _ "ret" _ _ (.vec (l.set n.toNat x)) hassert)).trans ?_
        iintro ⟨Hwand, Hty⟩
        iapply Hwand
        iexact Hty
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [vecSet, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    rcases hφ with rfl | rfl
    · exact Formula.wfIn_mono _ (by apply Formula.checkWf_ok; rfl) hsub hwf
    · exact Formula.wfIn_mono _ (by apply Formula.checkWf_ok; rfl) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [vecSet, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    have hresp : ρ.respects (some vecSetSym) := by
      have h := hdeps vecSet (by simp)
      simpa [vecSet] using h
    have hter : ∀ v i x : Runtime.Val,
        ((((ρ.updateConst .value "v" v).updateConst .value "i" i).updateConst
          .value "x" x).ternary .value .value .value .value "val_vec_set")
            = fun a b c => vecSetSym.interp (a, b, c) := by
      intro v i x
      rw [Env.updateConst_ternary, Env.updateConst_ternary, Env.updateConst_ternary]
      simpa [Env.respects, vecSetSym] using hresp
    rcases hφ with rfl | rfl
    · simp only [vecSetDefAxiom, Formula.all, Formula.eval]
      intro v i x
      simp only [terTerm, vecOf, intOf, vecSetSym, hter v i x, Term.eval, UnOp.eval, TerOp.eval,
        Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "v" ≠ "i" by decide),
        Env.lookupConst_updateConst_ne (show "v" ≠ "x" by decide),
        Env.lookupConst_updateConst_ne (show "i" ≠ "x" by decide), valVec, valInt]
      rfl
    · simp only [vecSetTypeAxiom, Formula.all, Formula.eval]
      intro v i x
      simp [terTerm, vecSetSym, hter v i x, Term.eval,
        Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "v" ≠ "i" by decide),
        Env.lookupConst_updateConst_ne (show "v" ≠ "x" by decide),
        Env.lookupConst_updateConst_ne (show "i" ≠ "x" by decide)]

/-! ## `Vec.make` -/

/-- `Vec.make : int -> 'a -> 'a vec`. Partial: the length must be nonnegative. -/
def vecMake : Intrinsic where
  arity  := .two
  name   := "val_vec_make"
  path   := some ("Vec", ["make"])
  reduce := Reduce.pure fun (n, x) r =>
    ∃ m, n = .int m ∧ 0 ≤ m ∧ r = .vec (List.replicate m.toNat x)
  wp     := fun (n, x) Q =>
    iprop(∃ m, ⌜n = .int m ∧ 0 ≤ m⌝ ∗ Q (.vec (List.replicate m.toNat x)))
  spec   :=
    { args  := [("n", .int), ("x", .tvar "a")]
      retTy := .vec (.tvar "a")
      pred  := .assert (.binpred .le (.const (.i 0)) (intOf "n")) <|
        .ret ("ret",
          .assert (.eq .value (.var .value "ret")
            (binTerm "val_vec_make" (.var .value "n") (.var .value "x"))) (.ret ())) }
  typing := fun _ tys =>
    match tys with
    | [_, t] => .ok [("a", t)]
    | _ => .error s!"expected 2 arguments, got {tys.length}"
  folSym := some vecMakeSym
  axioms := [⟨vecMakeDefAxiom, .high⟩, ⟨vecMakeTypeAxiom, .high⟩]

@[simp] theorem vecMake_arity : vecMake.arity = .two := rfl
@[simp] theorem vecMake_folSym : vecMake.folSym = some vecMakeSym := rfl

@[simp] theorem vecMake.toWp_eq (n x : Runtime.Val) (Q : Runtime.Val → iProp) :
    vecMake.toWp [n, x] Q =
      iprop(∃ m, ⌜n = .int m ∧ 0 ≤ m⌝ ∗ Q (.vec (List.replicate m.toNat x))) := rfl

@[simp] theorem vecMake.toReduce_eq (n x r : Runtime.Val) (μ μ' : TinyML.Heap) :
    vecMake.toReduce [n, x] μ r μ' =
      ((∃ m, n = .int m ∧ 0 ≤ m ∧ r = .vec (List.replicate m.toNat x)) ∧ μ' = μ) := rfl

@[simp] theorem vecMake.instantiate_args (σ : TinyML.TyVar → TinyML.Typ) :
    (vecMake.spec.instantiate σ).args = [("n", .int), ("x", σ "a")] := by
  simp [vecMake, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem vecMake.instantiate_retTy (σ : TinyML.TyVar → TinyML.Typ) :
    (vecMake.spec.instantiate σ).retTy = .vec (σ "a") := by
  simp [vecMake, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem vecMake.spec_pred :
    vecMake.spec.pred = .assert (.binpred .le (.const (.i 0)) (intOf "n"))
      (.ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (binTerm "val_vec_make" (.var .value "n") (.var .value "x"))) (.ret ()))) := rfl

instance : IntrinsicSound [vecMake] vecMake where
  specWf := fun _ hsub hwf =>
    specWf_of_base (by apply PredTrans.checkWf_ok; rfl) hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | [] => exact false_elim
    | [_] => exact false_elim
    | _ :: _ :: _ :: _ => exact false_elim
    | [n, x] =>
      have hred : ∀ m μ r μ',
          ctx vecMake.name [.int m, x] μ r μ'
            ↔ (0 ≤ m ∧ r = .vec (List.replicate m.toNat x)) ∧ μ' = μ := by
        intro m μ r μ'
        rw [hctx]
        simp only [vecMake.toReduce_eq]
        constructor
        · rintro ⟨⟨m', hn, hlo, hr⟩, hμ⟩
          cases hn
          exact ⟨⟨hlo, hr⟩, hμ⟩
        · rintro ⟨⟨hlo, hr⟩, hμ⟩
          exact ⟨⟨m, rfl, hlo, hr⟩, hμ⟩
      show iprop(∃ m, ⌜n = .int m ∧ 0 ≤ m⌝ ∗ Φ (.vec (List.replicate m.toNat x))) ⊢ _
      istart
      iintro ⟨%m, %ha, HΦ⟩
      obtain ⟨rfl, hlo⟩ := ha
      iapply (wp.prim_pure (hred m) ⟨_, hlo, rfl⟩)
      iintro %r %hr
      obtain ⟨_, rfl⟩ := hr
      iexact HΦ
  bridge := by
    intro _ σ Θ vs ρ Φ hρ
    simp only [vecMake.instantiate_args, vecMake.instantiate_retTy,
      Spec.instantiate_pred, vecMake.spec_pred, List.map_cons, List.map_nil]
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [n, x] =>
      simp only [PredTrans.apply, Assertion.pre]
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ n [x] _ _).1 $$ Hvs
      icases Hcons with ⟨Hn, Hrest⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ x [] _ _).1 $$ Hrest
      icases Hcons2 with ⟨Hx, _⟩
      ihave Hneq := (TinyML.ValHasType.int Θ n).1 $$ Hn
      ipure Hneq
      obtain ⟨m, rfl⟩ := Hneq
      icases Hpred with ⟨%hpre, Hpost⟩
      have hlo : 0 ≤ m := by
        simpa [intOf, Spec.argsEnv, Formula.eval, Term.eval,
          VerifM.Env.updateConst_env, Env.lookupConst_updateConst_same,
          Env.lookupConst_updateConst_ne (show "n" ≠ "x" by decide)] using hpre
      ihave Hty : iprop(TinyML.ValHasType Θ (Runtime.Val.vec (List.replicate m.toNat x))
          ((σ "a").vec)) $$ [Hx]
      · iapply (TinyML.ValHasType.vec_replicate Θ m.toNat x (σ "a"))
        iexact Hx
      simp only [vecMake.toWp_eq]
      iexists m
      isplitr [Hpost Hty]
      · ipureintro
        exact ⟨rfl, hlo⟩
      · have hassert : (Formula.eq .value (.var .value "ret")
            (binTerm "val_vec_make" (.var .value "n") (.var .value "x"))).eval
            ((Spec.argsEnv ρ [("n", TinyML.Typ.int), ("x", σ "a")] [.int m, x]).updateConst
              .value "ret" (.vec (List.replicate m.toNat x))).env := by
          have hargs := vec_respects_argsEnv_two
            [("n", TinyML.Typ.int), ("x", σ "a")] [Runtime.Val.int m, x] hρ
          have hbin : (Spec.argsEnv ρ [("n", TinyML.Typ.int), ("x", σ "a")]
              [.int m, x]).env.binary .value .value .value "val_vec_make"
                = fun a b => vecMakeSym.interp (a, b) := by
            simpa [Env.respects, vecMakeSym] using hargs
          show Runtime.Val.vec (List.replicate m.toNat x) =
            (Spec.argsEnv ρ [("n", TinyML.Typ.int), ("x", σ "a")]
              [.int m, x]).env.binary .value .value .value "val_vec_make" (.int m) x
          rw [hbin]
          simp [vecMakeSym, valInt, hlo]
        refine (sep_mono_left
          (assert_ret_apply Θ _ "ret" _ _ (.vec (List.replicate m.toNat x)) hassert)).trans ?_
        iintro ⟨Hwand, Hty⟩
        iapply Hwand
        iexact Hty
  axiomWf := by
    intro Δ hsub hwf a hφ
    simp only [vecMake, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    rcases hφ with rfl | rfl
    · exact Formula.wfIn_mono _ (by apply Formula.checkWf_ok; rfl) hsub hwf
    · exact Formula.wfIn_mono _ (by apply Formula.checkWf_ok; rfl) hsub hwf
  proof := by
    intro ρ hdeps a hφ
    simp only [vecMake, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    have hresp : ρ.respects (some vecMakeSym) := by
      have h := hdeps vecMake (by simp)
      simpa [vecMake] using h
    have hbin : ∀ n x : Runtime.Val,
        (((ρ.updateConst .value "n" n).updateConst .value "x" x).binary
          .value .value .value "val_vec_make") = fun a b => vecMakeSym.interp (a, b) := by
      intro n x
      rw [Env.updateConst_binary, Env.updateConst_binary]
      simpa [Env.respects, vecMakeSym] using hresp
    rcases hφ with rfl | rfl
    · simp only [vecMakeDefAxiom, Formula.all, Formula.eval]
      intro n x
      simp only [binTerm, intOf, vecMakeSym, hbin n x, Term.eval, UnOp.eval, BinOp.eval,
        Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "n" ≠ "x" by decide), valInt]
      rfl
    · simp only [vecMakeTypeAxiom, Formula.all, Formula.eval]
      intro n x
      simp [binTerm, vecMakeSym, hbin n x, Term.eval,
        Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "n" ≠ "x" by decide)]

end Intrinsics

end Stdlib

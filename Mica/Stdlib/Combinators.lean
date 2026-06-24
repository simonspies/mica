-- SUMMARY: Embeddings and the pure-intrinsic builders (`Pure.Zero`/`Pure.Unary`/`Pure.Binary`) that emit an intrinsic and its soundness instance, plus the shared helper lemmas their soundness proofs use.
import Mica.Verifier.Intrinsic

open Iris Iris.BI

namespace Stdlib

open Verifier

namespace Intrinsics

/-! # Combinators for intrinsic soundness -/

/-! ## Shared helpers -/

/-- Apply a `.ret (s, .assert φ ...)` spec at a value, discharging the asserted
    `φ` as a pure side condition. -/
private theorem assert_ret_apply [MicaGS HasLC.hasLC Sig] (Θ : TinyML.TypeEnv) (Φ : Runtime.Val → iProp)
    (s : String) (ρ : VerifM.Env) (φ : Formula) (v : Runtime.Val)
    (hφ : φ.eval (ρ.updateConst .value s v).env) :
    PredTrans.apply Θ Φ (.ret (s, .assert φ (.ret ()))) ρ ⊢ Φ v := by
  simp only [PredTrans.apply, Assertion.pre, Assertion.post]
  refine (forall_elim v).trans ?_
  iintro Hw
  iapply Hw
  ipureintro
  exact hφ

/-- A length-mismatched argument list makes the typing premise inconsistent, so
    it entails anything. -/
private theorem valsHaveTypes_off_shape [MicaGS HasLC.hasLC Sig] {Θ : TinyML.TypeEnv}
    {vs : List Runtime.Val} {tys : List TinyML.Typ} (P : iProp)
    (hlen : vs.length ≠ tys.length) :
    TinyML.ValsHaveTypes Θ vs tys ⊢ P := by
  refine TinyML.ValsHaveTypes.length_eq.trans ?_
  iintro %h
  simp at h; omega

/-- Respect for an arity-one symbol survives the argument-binding fold; each
    step rebinds a `value` constant, which never touches the unary table. -/
private theorem respects_argsEnv_one {s : FOL.Symbol .one} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (_, _) :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine respects_argsEnv_one rest vs ?_
      rw [VerifM.Env.updateConst_env]
      simpa only [Env.respects, Env.updateConst_unary] using h

/-- Respect for an arity-two symbol survives the argument-binding fold; each
    step rebinds a `value` constant, which never touches the binary table. -/
private theorem respects_argsEnv_two {s : FOL.Symbol .two} :
    ∀ (args : List (String × TinyML.Typ)) (vs : List Runtime.Val) {ρ : VerifM.Env},
      ρ.env.respects (some s) → (Spec.argsEnv ρ args vs).env.respects (some s)
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | (_, _) :: rest, _ :: vs, ρ, h => by
      simp only [Spec.argsEnv]
      refine respects_argsEnv_two rest vs ?_
      rw [VerifM.Env.updateConst_env]
      simpa only [Env.respects, Env.updateConst_binary] using h

/-! ## `specWf`: predicate-transformer well-formedness -/

/-- The `specWf` obligation from a base well-formedness fact in the singleton
    signature: monotonicity carries it to any signature declaring the symbol. -/
private theorem specWf_of_base {i : Intrinsic}
    (hbase : PredTrans.wfIn
      ((Intrinsic.sigOf [i]).declVars (Spec.argVars i.specArgs)) i.spec.pred)
    {Δ : Signature} (hsub : (Signature.empty.extendWithSym i.folSym).Subset Δ) (hwf : Δ.wf) :
    PredTrans.wfIn (Δ.declVars (Spec.argVars i.specArgs)) i.spec.pred :=
  PredTrans.wfIn_mono hbase
    (Signature.Subset.declVars hsub (Spec.argVars i.specArgs))
    (Signature.wf_declVars hwf)

/-! ## Embeddings: Lean types embedded into values

A `Embedding` records how a Lean carrier type sits inside `Runtime.Val` at a
given TinyML type: an injection, a matching projection, and the `is-of`
predicate that recognizes the type at the value sort. The coherence laws
live in `Embedding.Lawful`. -/

/-- How a Lean carrier is represented as runtime values of a TinyML type: an
    injection, its retracting projection, and the `is-of` value-sort predicate
    recognizing the type. Pure data; see `Embedding.Lawful` for the laws. -/
structure Embedding where
  typ     : TinyML.Typ
  carrier : Type
  inject  : carrier → Runtime.Val
  project : Runtime.Val → carrier
  isOf    : UnPred .value

/-- Integer projection of a runtime value, matching FOL's `toInt`. -/
def valInt : Runtime.Val → Int
  | .int n => n
  | _      => 0

/-- Boolean projection of a runtime value, matching FOL's `toBool`. -/
def valBool : Runtime.Val → Bool
  | .bool b => b
  | _       => false

/-- Byte-string projection of a runtime value, matching FOL's `toString`. -/
def valStr : Runtime.Val → List UInt8
  | .str s => s
  | _      => []

/-- Float projection of a runtime value, matching FOL's `toFloat`. -/
def valFloat : Runtime.Val → UInt64
  | .float b => b
  | _        => 0

/-- Integers as `.int` values. -/
def Embedding.int  : Embedding := ⟨.int,    Int,        .int,  valInt,  .isInt⟩
/-- Booleans as `.bool` values. -/
def Embedding.bool : Embedding := ⟨.bool,   Bool,       .bool, valBool, .isBool⟩
/-- Byte strings as `.str` values. -/
def Embedding.str  : Embedding := ⟨.string, List UInt8, .str,  valStr,  .isStr⟩
/-- IEEE binary64 bit-patterns as `.float` values. -/
def Embedding.float : Embedding := ⟨.float, UInt64, .float, valFloat, .isFloat⟩

/-- Coherence laws for an `Embedding`. -/
structure Embedding.Lawful (e : Embedding) where
  project_inject : ∀ x, e.project (e.inject x) = x
  isOf_wf        : ∀ Δ, e.isOf.wfIn Δ
  isOf_inject    : ∀ (ρ : Env) (x : e.carrier), UnPred.eval ρ e.isOf (e.inject x)
  member         : ∀ [MicaGS HasLC.hasLC Sig] (Θ : TinyML.TypeEnv) (w : Runtime.Val),
                     TinyML.ValHasType Θ w e.typ ⊣⊢ iprop(⌜∃ x, w = e.inject x⌝)
  intro          : ∀ [MicaGS HasLC.hasLC Sig] (Θ : TinyML.TypeEnv) (x : e.carrier),
                     ⊢ TinyML.ValHasType Θ (e.inject x) e.typ

/-- Integers are a lawful embedding. -/
def Embedding.lawfulInt : Embedding.int.Lawful where
  project_inject _ := rfl
  isOf_wf _ := trivial
  isOf_inject _ _ := by simp [Embedding.int]
  member Θ w := TinyML.ValHasType.int Θ w
  intro Θ x := TinyML.ValHasType.int_intro Θ x

/-- Booleans are a lawful embedding. -/
def Embedding.lawfulBool : Embedding.bool.Lawful where
  project_inject _ := rfl
  isOf_wf _ := trivial
  isOf_inject _ _ := by simp [Embedding.bool]
  member Θ w := TinyML.ValHasType.bool Θ w
  intro Θ x := TinyML.ValHasType.bool_intro Θ x

/-- Byte strings are a lawful embedding. -/
def Embedding.lawfulStr : Embedding.str.Lawful where
  project_inject _ := rfl
  isOf_wf _ := trivial
  isOf_inject _ _ := by simp [Embedding.str]
  member Θ w := TinyML.ValHasType.string Θ w
  intro Θ x := TinyML.ValHasType.string_intro Θ x

/-- Floats are a lawful embedding. -/
def Embedding.lawfulFloat : Embedding.float.Lawful where
  project_inject _ := rfl
  isOf_wf _ := trivial
  isOf_inject _ _ := by simp [Embedding.float]
  member Θ w := TinyML.ValHasType.float Θ w
  intro Θ x := TinyML.ValHasType.float_intro Θ x

namespace Pure

/-! ## Builder for pure zero-arity intrinsics

`Pure.Zero` bundles the *computational* content of a pure constant intrinsic:
its name/path, result embedding, carrier value, and SMT defining axiom. From
this alone the `Intrinsic` and its FOL symbol are built (`toIntrinsic`). The
proof obligations live in `Pure.Zero.Lawful`. -/

/-- The computational data of a pure zero-arity intrinsic. -/
structure Zero where
  name     : String
  path     : Option (String × List String)
  res      : Embedding
  f        : res.carrier
  defAxiom : Formula

/-- The intrinsic's uninterpreted constant symbol as a value term. -/
def Zero.opTerm (b : Zero) : Term .value :=
  .const (.uninterpreted b.name .value)

/-- The FOL symbol: the standard interpretation injects the carrier value. -/
def Zero.sym (b : Zero) : FOL.Symbol .zero where
  name   := b.name
  interp := fun () => b.res.inject b.f

/-- The result-typing axiom, generated from `res`. -/
def Zero.typeAxiom (b : Zero) : Formula :=
  .unpred b.res.isOf b.opTerm

/-- The intrinsic built from `b`: a literal `Intrinsic.mk`. -/
def Zero.toIntrinsic (b : Zero) : Intrinsic where
  arity  := .zero
  name   := b.name
  path   := b.path
  reduce := Reduce.pure fun () v => v = b.res.inject b.f
  wp     := fun () Q => Q (b.res.inject b.f)
  spec   :=
    { args  := []
      retTy := b.res.typ
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") b.opTerm) (.ret ())) }
  folSym := some b.sym
  axioms := [b.defAxiom, b.typeAxiom]

@[simp] theorem Zero.toWp_eq (b : Zero) (Q : Runtime.Val → iProp) :
    b.toIntrinsic.toWp [] Q = Q (b.res.inject b.f) := rfl

@[simp] theorem Zero.toReduce_eq (b : Zero) (v : Runtime.Val) (μ μ' : TinyML.Heap) :
    b.toIntrinsic.toReduce [] μ v μ' = (v = b.res.inject b.f ∧ μ' = μ) := rfl

/-- Proof obligations for a pure zero-arity intrinsic. The `nameFresh` premise
    keeps the generated constant symbol distinct from the spec's `"ret"`
    binder, since both live in the value-constant namespace. -/
structure Zero.Lawful (b : Zero) where
  resL       : b.res.Lawful
  nameFresh  : b.name ≠ "ret"
  specBaseWf : PredTrans.wfIn
                 ((Intrinsic.sigOf [b.toIntrinsic]).declVars
                   (Spec.argVars b.toIntrinsic.specArgs)) b.toIntrinsic.spec.pred
  defWf      : b.defAxiom.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  typeWf     : b.typeAxiom.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  defEval    : ∀ ρ : Env, ρ.respects (some b.sym) → Formula.eval ρ b.defAxiom

/-- The `IntrinsicSound` instance for a pure zero-arity intrinsic. -/
@[reducible] def Zero.Lawful.sound {b : Zero} (l : b.Lawful) :
    IntrinsicSound [b.toIntrinsic] b.toIntrinsic where
  specWf := fun _ hsub hwf => specWf_of_base l.specBaseWf hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | _ :: _ => exact false_elim
    | [] =>
      have hred : ∀ μ v μ',
          ctx b.toIntrinsic.name [] μ v μ' ↔ v = b.res.inject b.f ∧ μ' = μ := by
        intro μ v μ'
        rw [hctx]
        simp only [Zero.toIntrinsic, Intrinsic.toReduce_zero_of_arity, Reduce.pure]
      rw [Zero.toWp_eq]
      istart
      iintro HΦ
      iapply (wp.prim_pure hred ⟨b.res.inject b.f, rfl⟩)
      iintro %v %hv
      subst hv
      iexact HΦ
  bridge := by
    intro _ Θ vs ρ Φ hρ
    show TinyML.ValsHaveTypes Θ vs [] ∗ _ ⊢ _
    match vs with
    | _ :: _ => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [] =>
      simp only [Zero.toIntrinsic, Intrinsic.toWp_zero_of_arity]
      refine (sep_mono_left (TinyML.ValsHaveTypes.nil Θ).1).trans ?_
      refine emp_sep.1.trans ?_
      refine (assert_ret_apply Θ _ "ret" _ _ (b.res.inject b.f) ?_).trans ?_
      · have hconst : (ρ.updateConst .value "ret" (b.res.inject b.f)).env.lookupConst
            .value b.name = b.res.inject b.f := by
          rw [VerifM.Env.updateConst_env]
          rw [Env.lookupConst_updateConst_ne l.nameFresh]
          simpa [Env.respects, Zero.sym] using hρ
        simpa [Zero.opTerm, Term.eval, Const.denote] using hconst.symm
      · iintro Hwand
        iapply Hwand
        exact l.resL.intro Θ b.f
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [Zero.toIntrinsic, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    rcases hφ with rfl | rfl
    · exact Formula.wfIn_mono _ l.defWf hsub hwf
    · exact Formula.wfIn_mono _ l.typeWf hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [Zero.toIntrinsic, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    have hresp : ρ.respects (some b.sym) := by
      have h := hdeps b.toIntrinsic (by simp)
      simpa [Zero.toIntrinsic] using h
    rcases hφ with rfl | rfl
    · exact l.defEval ρ hresp
    · simp only [Zero.typeAxiom, Formula.eval, Zero.opTerm, Term.eval, Const.denote]
      have hconst : ρ.consts .value b.name = b.res.inject b.f := by
        simpa [Env.respects, Env.lookupConst, Zero.sym] using hresp
      rw [hconst]
      exact l.resL.isOf_inject _ _

/-! ## Builder for pure unary intrinsics

`Pure.Unary` bundles the *computational* content of a pure unary intrinsic: its
name/path, the argument and result embeddings, the carrier function `f`, and the
SMT defining axiom. From this alone the `Intrinsic` and its FOL symbol are built
(`toIntrinsic`). The proof obligations live in `Pure.Unary.Lawful`. -/

/-- The computational data of a pure unary intrinsic. -/
structure Unary where
  name     : String
  path     : Option (String × List String)
  arg      : Embedding
  res      : Embedding
  f        : arg.carrier → res.carrier
  defAxiom : Formula

/-- The intrinsic's uninterpreted unary symbol applied to a value term. -/
def Unary.opTerm (b : Unary) (x : Term .value) : Term .value :=
  .unop (.uninterpreted b.name .value .value) x

/-- The FOL symbol: the standard interpretation projects, applies `f`, injects. -/
def Unary.sym (b : Unary) : FOL.Symbol .one where
  name   := b.name
  interp := fun a => b.res.inject (b.f (b.arg.project a))

/-- The result-typing axiom, generated from `res`. -/
def Unary.typeAxiom (b : Unary) : Formula :=
  .forall_ "a" .value [.term (b.opTerm (.var .value "a"))] <|
    .unpred b.res.isOf (b.opTerm (.var .value "a"))

/-- The intrinsic built from `b`: a literal `Intrinsic.mk`. -/
def Unary.toIntrinsic (b : Unary) : Intrinsic where
  arity  := .one
  name   := b.name
  path   := b.path
  reduce := Reduce.pure fun a v => ∃ x, a = b.arg.inject x ∧ v = b.res.inject (b.f x)
  wp     := fun a Q => iprop(∃ x, ⌜a = b.arg.inject x⌝ ∗ Q (b.res.inject (b.f x)))
  spec   :=
    { args  := [("a", b.arg.typ)]
      retTy := b.res.typ
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a"))) (.ret ())) }
  folSym := some b.sym
  axioms := [b.defAxiom, b.typeAxiom]

@[simp] theorem Unary.toWp_eq (b : Unary) (a : Runtime.Val) (Q : Runtime.Val → iProp) :
    b.toIntrinsic.toWp [a] Q = iprop(∃ x, ⌜a = b.arg.inject x⌝ ∗ Q (b.res.inject (b.f x))) := rfl

@[simp] theorem Unary.toReduce_eq (b : Unary) (a v : Runtime.Val) (μ μ' : TinyML.Heap) :
    b.toIntrinsic.toReduce [a] μ v μ' = ((∃ x, a = b.arg.inject x ∧ v = b.res.inject (b.f x)) ∧ μ' = μ) := rfl

/-- Proof obligations for a pure unary intrinsic. -/
structure Unary.Lawful (b : Unary) where
  argL       : b.arg.Lawful
  resL       : b.res.Lawful
  specBaseWf : PredTrans.wfIn
                 ((Intrinsic.sigOf [b.toIntrinsic]).declVars
                   (Spec.argVars b.toIntrinsic.specArgs)) b.toIntrinsic.spec.pred
  defWf      : b.defAxiom.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  typeWf     : b.typeAxiom.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  defEval    : ∀ ρ : Env, ρ.respects (some b.sym) → Formula.eval ρ b.defAxiom

/-- The `IntrinsicSound` instance for a pure unary intrinsic. -/
@[reducible] def Unary.Lawful.sound {b : Unary} (l : b.Lawful) :
    IntrinsicSound [b.toIntrinsic] b.toIntrinsic where
  specWf := fun _ hsub hwf => specWf_of_base l.specBaseWf hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | [] => exact false_elim
    | _ :: _ :: _ => exact false_elim
    | [a] =>
      have hred : ∀ x μ v μ',
          ctx b.toIntrinsic.name [b.arg.inject x] μ v μ'
            ↔ v = b.res.inject (b.f x) ∧ μ' = μ := by
        intro x μ v μ'
        rw [hctx]
        simp only [Unary.toIntrinsic, Intrinsic.toReduce_one_of_arity, Reduce.pure]
        constructor
        · rintro ⟨⟨x', hx, hv⟩, hμ⟩
          have hxx : x = x' := by
            have := congrArg b.arg.project hx
            rwa [l.argL.project_inject, l.argL.project_inject] at this
          subst hxx
          exact ⟨hv, hμ⟩
        · rintro ⟨hv, hμ⟩
          exact ⟨⟨x, rfl, hv⟩, hμ⟩
      show iprop(∃ x, ⌜a = b.arg.inject x⌝ ∗ Φ (b.res.inject (b.f x))) ⊢ _
      istart
      iintro ⟨%x, %ha, HΦ⟩
      obtain rfl := ha
      iapply (wp.prim_pure (hred x) ⟨_, rfl⟩)
      iintro %v %hv
      subst hv
      iexact HΦ
  bridge := by
    intro _ Θ vs ρ Φ hρ
    show TinyML.ValsHaveTypes Θ vs [b.arg.typ] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [v] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv, _⟩
      ihave Hveq := (l.argL.member Θ v).1 $$ Hv
      ipure Hveq
      obtain ⟨x, rfl⟩ := Hveq
      simp only [Unary.toIntrinsic, Intrinsic.toWp_one_of_arity]
      iexists x
      isplitr [Hpred]
      · ipureintro; rfl
      · have hassert : (Formula.eq .value (.var .value "ret")
            (b.opTerm (.var .value "a"))).eval
            ((Spec.argsEnv ρ b.toIntrinsic.specArgs [b.arg.inject x]).updateConst
              .value "ret" (b.res.inject (b.f x))).env := by
          have hargs := respects_argsEnv_one b.toIntrinsic.specArgs [b.arg.inject x] hρ
          have hun : (Spec.argsEnv ρ b.toIntrinsic.specArgs [b.arg.inject x]).env.unary
              .value .value b.name = b.sym.interp := by
            simpa [Env.respects, Unary.sym] using hargs
          show b.res.inject (b.f x) =
            (Spec.argsEnv ρ b.toIntrinsic.specArgs [b.arg.inject x]).env.unary
              .value .value b.name (b.arg.inject x)
          simp [hun, Unary.sym, l.argL.project_inject]
        refine (assert_ret_apply Θ _ "ret" _ _ (b.res.inject (b.f x)) hassert).trans ?_
        iintro Hwand
        iapply Hwand
        exact l.resL.intro Θ (b.f x)
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [Unary.toIntrinsic, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    rcases hφ with rfl | rfl
    · exact Formula.wfIn_mono _ l.defWf hsub hwf
    · exact Formula.wfIn_mono _ l.typeWf hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [Unary.toIntrinsic, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    have hresp : ρ.respects (some b.sym) := by
      have h := hdeps b.toIntrinsic (by simp)
      simpa [Unary.toIntrinsic] using h
    rcases hφ with rfl | rfl
    · exact l.defEval ρ hresp
    · simp only [Unary.typeAxiom, Formula.eval]
      intro x
      have hu : (ρ.updateConst .value "a" x).unary .value .value b.name = b.sym.interp := by
        rw [Env.updateConst_unary]
        simpa [Unary.sym] using hresp
      simp only [Unary.opTerm, Term.eval, UnOp.eval, Env.lookupConst_updateConst_same,
        hu, Unary.sym]
      exact l.resL.isOf_inject _ _

/-! ## Builder for pure binary intrinsics

`Pure.Binary` bundles the *computational* content of a pure binary intrinsic:
its name/path, the argument and result embeddings, the carrier function `f`, and
the SMT defining axiom. From this alone the `Intrinsic` and its FOL symbol are
built (`toIntrinsic`). The proof obligations live in `Pure.Binary.Lawful`. -/

/-- The computational data of a pure binary intrinsic. -/
structure Binary where
  name     : String
  path     : Option (String × List String)
  arg      : Embedding
  res      : Embedding
  f        : arg.carrier → arg.carrier → res.carrier
  defAxiom : Formula

/-- The intrinsic's uninterpreted binary symbol applied to two value terms. -/
def Binary.opTerm (b : Binary) (x y : Term .value) : Term .value :=
  .binop (.uninterpreted b.name .value .value .value) x y

/-- The FOL symbol: the standard interpretation projects both arguments, applies
    `f`, and injects the result. -/
def Binary.sym (b : Binary) : FOL.Symbol .two where
  name   := b.name
  interp := fun (a, c) => b.res.inject (b.f (b.arg.project a) (b.arg.project c))

/-- The result-typing axiom, generated from `res`: the op result satisfies the
    result embedding's `is-of` predicate. -/
def Binary.typeAxiom (b : Binary) : Formula :=
  .all "a" .value <| .forall_ "b" .value
    [.term (b.opTerm (.var .value "a") (.var .value "b"))] <|
    .unpred b.res.isOf (b.opTerm (.var .value "a") (.var .value "b"))

/-- The intrinsic built from `b`: a literal `Intrinsic.mk` so the arity-unfolding
    lemmas (`toReduce_two_of_arity`, `toWp_two_of_arity`) keep firing by `rfl`. -/
def Binary.toIntrinsic (b : Binary) : Intrinsic where
  arity  := .two
  name   := b.name
  path   := b.path
  reduce := Reduce.pure fun (a, c) v =>
    ∃ x y, a = b.arg.inject x ∧ c = b.arg.inject y ∧ v = b.res.inject (b.f x y)
  wp     := fun (a, c) Q =>
    iprop(∃ x y, ⌜a = b.arg.inject x ∧ c = b.arg.inject y⌝ ∗ Q (b.res.inject (b.f x y)))
  spec   :=
    { args  := [("a", b.arg.typ), ("b", b.arg.typ)]
      retTy := b.res.typ
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret")
          (b.opTerm (.var .value "a") (.var .value "b"))) (.ret ())) }
  folSym := some b.sym
  axioms := [b.defAxiom, b.typeAxiom]

@[simp] theorem Binary.toWp_eq (b : Binary) (a c : Runtime.Val) (Q : Runtime.Val → iProp) :
    b.toIntrinsic.toWp [a, c] Q =
      iprop(∃ x y, ⌜a = b.arg.inject x ∧ c = b.arg.inject y⌝ ∗ Q (b.res.inject (b.f x y))) := rfl

@[simp] theorem Binary.toReduce_eq (b : Binary) (a c v : Runtime.Val) (μ μ' : TinyML.Heap) :
    b.toIntrinsic.toReduce [a, c] μ v μ' =
      ((∃ x y, a = b.arg.inject x ∧ c = b.arg.inject y ∧ v = b.res.inject (b.f x y)) ∧ μ' = μ) := rfl

/-- Proof obligations for a pure binary intrinsic: lawful embeddings, the three
    well-formedness facts (spec/def-axiom/type-axiom — one-liners at literal
    names), and validity of the defining axiom under the standard
    interpretation. -/
structure Binary.Lawful (b : Binary) where
  argL       : b.arg.Lawful
  resL       : b.res.Lawful
  specBaseWf : PredTrans.wfIn
                 ((Intrinsic.sigOf [b.toIntrinsic]).declVars
                   (Spec.argVars b.toIntrinsic.specArgs)) b.toIntrinsic.spec.pred
  defWf      : b.defAxiom.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  typeWf     : b.typeAxiom.wfIn (Intrinsic.sigOf [b.toIntrinsic])
  defEval    : ∀ ρ : Env, ρ.respects (some b.sym) → Formula.eval ρ b.defAxiom

/-- The whole `IntrinsicSound` instance for a pure binary intrinsic. -/
@[reducible] def Binary.Lawful.sound {b : Binary} (l : b.Lawful) :
    IntrinsicSound [b.toIntrinsic] b.toIntrinsic where
  specWf := fun _ hsub hwf => specWf_of_base l.specBaseWf hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | [] => exact false_elim
    | [_] => exact false_elim
    | _ :: _ :: _ :: _ => exact false_elim
    | [a, c] =>
      have hred : ∀ x y μ v μ',
          ctx b.toIntrinsic.name [b.arg.inject x, b.arg.inject y] μ v μ'
            ↔ v = b.res.inject (b.f x y) ∧ μ' = μ := by
        intro x y μ v μ'
        rw [hctx]
        simp only [Binary.toIntrinsic, Intrinsic.toReduce_two_of_arity, Reduce.pure]
        constructor
        · rintro ⟨⟨x', y', hx, hy, hv⟩, hμ⟩
          have hxx : x = x' := by
            have := congrArg b.arg.project hx
            rwa [l.argL.project_inject, l.argL.project_inject] at this
          have hyy : y = y' := by
            have := congrArg b.arg.project hy
            rwa [l.argL.project_inject, l.argL.project_inject] at this
          subst hxx; subst hyy
          exact ⟨hv, hμ⟩
        · rintro ⟨hv, hμ⟩
          exact ⟨⟨x, y, rfl, rfl, hv⟩, hμ⟩
      show iprop(∃ x y, ⌜a = b.arg.inject x ∧ c = b.arg.inject y⌝ ∗ Φ (b.res.inject (b.f x y))) ⊢ _
      istart
      iintro ⟨%x, %y, %hab, HΦ⟩
      obtain ⟨rfl, rfl⟩ := hab
      iapply (wp.prim_pure (hred x y) ⟨_, rfl⟩)
      iintro %v %hv
      subst hv
      iexact HΦ
  bridge := by
    intro _ Θ vs ρ Φ hρ
    show TinyML.ValsHaveTypes Θ vs [b.arg.typ, b.arg.typ] ∗ _ ⊢ _
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [_] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [v1, v2] =>
      iintro ⟨Hvs, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v1 [v2] _ _).1 $$ Hvs
      icases Hcons with ⟨Hv1, Hvs2⟩
      ihave Hcons2 := (TinyML.ValsHaveTypes.cons Θ v2 [] _ _).1 $$ Hvs2
      icases Hcons2 with ⟨Hv2, _⟩
      ihave Hv1eq := (l.argL.member Θ v1).1 $$ Hv1
      ipure Hv1eq
      ihave Hv2eq := (l.argL.member Θ v2).1 $$ Hv2
      ipure Hv2eq
      obtain ⟨x, rfl⟩ := Hv1eq
      obtain ⟨y, rfl⟩ := Hv2eq
      simp only [Binary.toIntrinsic, Intrinsic.toWp_two_of_arity]
      iexists x
      iexists y
      isplitr [Hpred]
      · ipureintro; exact ⟨rfl, rfl⟩
      · have hassert : (Formula.eq .value (.var .value "ret")
            (b.opTerm (.var .value "a") (.var .value "b"))).eval
            ((Spec.argsEnv ρ b.toIntrinsic.specArgs
              [b.arg.inject x, b.arg.inject y]).updateConst
              .value "ret" (b.res.inject (b.f x y))).env := by
          have hargs := respects_argsEnv_two b.toIntrinsic.specArgs
            [b.arg.inject x, b.arg.inject y] hρ
          have hbin : (Spec.argsEnv ρ b.toIntrinsic.specArgs
              [b.arg.inject x, b.arg.inject y]).env.binary .value .value .value b.name
              = fun a c => b.sym.interp (a, c) := by
            simpa [Env.respects, Binary.sym] using hargs
          show b.res.inject (b.f x y) =
            (Spec.argsEnv ρ b.toIntrinsic.specArgs
              [b.arg.inject x, b.arg.inject y]).env.binary
              .value .value .value b.name (b.arg.inject x) (b.arg.inject y)
          simp [hbin, Binary.sym, l.argL.project_inject]
        refine (assert_ret_apply Θ _ "ret" _ _ (b.res.inject (b.f x y)) hassert).trans ?_
        iintro Hwand
        iapply Hwand
        exact l.resL.intro Θ (b.f x y)
  axiomWf := by
    intro Δ hsub hwf φ hφ
    simp only [Binary.toIntrinsic, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    rcases hφ with rfl | rfl
    · exact Formula.wfIn_mono _ l.defWf hsub hwf
    · exact Formula.wfIn_mono _ l.typeWf hsub hwf
  proof := by
    intro ρ hdeps φ hφ
    simp only [Binary.toIntrinsic, List.mem_cons, List.not_mem_nil, _root_.or_false] at hφ
    have hresp : ρ.respects (some b.sym) := by
      have h := hdeps b.toIntrinsic (by simp)
      simpa [Binary.toIntrinsic] using h
    rcases hφ with rfl | rfl
    · exact l.defEval ρ hresp
    · simp only [Binary.typeAxiom, Formula.all, Formula.eval]
      intro x y
      have hb : ((ρ.updateConst .value "a" x).updateConst .value "b" y).binary
          .value .value .value b.name = fun a c => b.sym.interp (a, c) := by
        rw [Env.updateConst_binary, Env.updateConst_binary]
        simpa [Binary.sym] using hresp
      simp only [Binary.opTerm, Term.eval, BinOp.eval, Env.lookupConst_updateConst_same,
        Env.lookupConst_updateConst_ne (show "a" ≠ "b" by decide), hb, Binary.sym]
      exact l.resL.isOf_inject _ _

end Pure

syntax (name := intrinsicDefEval) "intrinsic_def_eval" "["
  ((Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),*,?) "]" : tactic

macro_rules
  | `(tactic| intrinsic_def_eval [$xs,*]) => `(tactic|
  ((intro ρ; intro hρ);
   simp_all [Env.respects, Formula.eval, Formula.all, Term.eval, Env.lookupConst,
     Env.updateConst, Env.updateConst_unary, Env.updateConst_binary,
     Env.lookupConst_updateConst_same, Pure.Zero.sym, Pure.Unary.sym, Pure.Binary.sym,
     Embedding.int, Embedding.bool, Embedding.str, Embedding.float,
     Const.denote, valInt, valBool, valStr, valFloat, $xs,*]))

end Intrinsics
end Stdlib

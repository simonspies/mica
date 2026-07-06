-- SUMMARY: `Fun.id`
import Mica.Stdlib.Combinators

open Iris Iris.BI

/-!
# Functions

The indentity function as an example exercising the support for implementing
polymorphic intrinsics.

-/

namespace Stdlib

open Verifier

namespace Intrinsics

/-! ## `Fun.id` -/

/-- `Fun.id : 'a -> 'a`, the polymorphic identity. -/
def funId : Intrinsic where
  arity  := .one
  name   := "fun_id"
  path   := some ("Fun", ["id"])
  reduce := Reduce.pure fun a v => v = a
  wp     := fun a Q => Q a
  spec   :=
    { args  := [("x", .tvar "a")]
      retTy := .tvar "a"
      pred  := .ret ("ret",
        .assert (.eq .value (.var .value "ret") (.var .value "x")) (.ret ())) }
  typing := fun _ tys =>
    match tys with
    | [t] => .ok [("a", t)]
    | _ => .error s!"expected 1 argument, got {tys.length}"
  folSym := none
  axioms := []

@[simp] theorem funId_folSym : funId.folSym = none := rfl

@[simp] theorem funId.toWp_eq (a : Runtime.Val) (Q : Runtime.Val → iProp) :
    funId.toWp [a] Q = Q a := rfl

@[simp] theorem funId.toReduce_eq (a v : Runtime.Val) (μ μ' : TinyML.Heap) :
    funId.toReduce [a] μ v μ' = (v = a ∧ μ' = μ) := rfl

@[simp] theorem funId.instantiate_args (σ : TinyML.TyVar → TinyML.Typ) :
    (funId.spec.instantiate σ).args = [("x", σ "a")] := by
  simp [funId, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem funId.instantiate_retTy (σ : TinyML.TyVar → TinyML.Typ) :
    (funId.spec.instantiate σ).retTy = σ "a" := by
  simp [funId, Spec.instantiate, TinyML.Typ.subst]

@[simp] theorem funId.spec_pred :
    funId.spec.pred = .ret ("ret",
      .assert (.eq .value (.var .value "ret") (.var .value "x")) (.ret ())) := rfl

instance : IntrinsicSound [funId] funId where
  specWf := fun _ hsub hwf =>
    specWf_of_base (by apply PredTrans.checkWf_ok; rfl) hsub hwf
  wp_sound := by
    intro _ ctx hctx vs Φ
    match vs with
    | [] => exact false_elim
    | _ :: _ :: _ => exact false_elim
    | [a] =>
      have hred : ∀ μ v μ', ctx funId.name [a] μ v μ' ↔ v = a ∧ μ' = μ := by
        intro μ v μ'
        rw [hctx]
        simp only [funId.toReduce_eq]
      show Φ a ⊢ _
      istart
      iintro HΦ
      iapply (wp.prim_pure hred ⟨a, rfl⟩)
      iintro %v %hv
      subst hv
      iexact HΦ
  bridge := by
    intro _ σ Θ vs ρ Φ _hρ
    simp only [funId.instantiate_args, funId.instantiate_retTy,
      Spec.instantiate_pred, funId.spec_pred, List.map_cons, List.map_nil]
    match vs with
    | [] => exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | _ :: _ :: _ =>
        exact (sep_mono_left (valsHaveTypes_off_shape _ (by simp))).trans sep_elim_left
    | [v] =>
      have hφ : (Formula.eq .value (.var .value "ret") (.var .value "x")).eval
          ((Spec.argsEnv ρ [("x", σ "a")] [v]).updateConst .value "ret" v).env := by
        simp [Spec.argsEnv, Formula.eval, Term.eval, VerifM.Env.updateConst_env,
          Env.lookupConst_updateConst_same, Env.lookupConst_updateConst_ne]
      iintro ⟨Hvals, Hpred⟩
      ihave Hcons := (TinyML.ValsHaveTypes.cons Θ v [] _ _).1 $$ Hvals
      icases Hcons with ⟨Hv, _⟩
      ihave Hwand := (assert_ret_apply Θ _ "ret" _ _ v hφ) $$ Hpred
      simp only [funId.toWp_eq]
      iapply Hwand
      iexact Hv
  axiomWf := by
    intro _ _ _ a ha
    simp [funId] at ha
  proof := by
    intro ρ _ a ha
    simp [funId] at ha

end Intrinsics

end Stdlib

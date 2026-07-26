-- SUMMARY: Semantics of atoms, assertions, and specifications, interpreting types by the logical relation.
import Mica.SourceTinyML.Assertions
import Mica.SourceTinyML.LogicalRelation
import Mica.FOL.SpecFn

open Iris Iris.BI Iris.OFE

variable [MicaGS HasLC.hasLC Sig]

/-!
# Specification semantics

The Iris meaning of the assertion syntax in `Mica/SourceTinyML/Assertions.lean`,
up to `Spec.isPrecondFor`, the predicate saying that a runtime value satisfies a
specification. Types are interpreted by the logical relation of the world the
semantics is taken in.

The verifier operations on the same syntax — `toItem`, `resolve`,
`assume`/`prove`, `call`/`implement` — and all well-formedness conditions and
correctness proofs live in `Mica/Verifier/`.
-/

-- ---------------------------------------------------------------------------
-- Atoms
-- ---------------------------------------------------------------------------

def Atom.eval (W : TinyML.World) {τ : Srt} (p : Atom TinyML.Typ τ) (ρ : Env) : τ.denote → iProp :=
  match p with
  | isint t  => λ v => ⌜.int v = t.eval ρ⌝
  | isbool t => λ v => ⌜.bool v = t.eval ρ⌝
  | isinj tag arity t => λ v => ⌜.inj tag arity v = t.eval ρ⌝
  | own l ty => λ v => ∃ loc : Runtime.Location,
      ⌜l.eval ρ = .loc loc⌝ ∗ loc ↦ [v] ∗ TinyML.ValHasType W v ty
  | arr a ty => λ v => ∃ loc : Runtime.Location, ∃ vs : List Runtime.Val,
      ⌜a.eval ρ = .array vs.length loc⌝ ∗ ⌜v = .vec vs⌝ ∗ loc ↦ vs ∗
        TinyML.ValHasType W (.vec vs) (.vec ty)
  | rel name arg => λ v =>
    ⌜(SpecFn.isDefined name arg).eval ρ ∧ (SpecFn.call name arg).eval ρ = v⌝

-- ---------------------------------------------------------------------------
-- Assertions
-- ---------------------------------------------------------------------------

def Assertion.pre (W : TinyML.World) (Φ : α → Env → iProp) (m : Assertion TinyML.Typ α) (ρ : Env) : iProp :=
  (match m with
  | .ret a        => Φ a ρ
  | .assert φ k   => ⌜φ.eval ρ⌝ ∗ Assertion.pre W Φ k ρ
  | .let_ x t k   => let v := t.eval ρ; Assertion.pre W Φ k (ρ.updateConst x.sort x.name v)
  | .pred x p k   => ∃ (v : x.sort.denote), p.eval W ρ v ∗ Assertion.pre W Φ k (ρ.updateConst x.sort x.name v)
  | .ite φ kt ke  =>
      iprop((⌜φ.eval ρ⌝ -∗ Assertion.pre W Φ kt ρ) ∧
            (⌜¬ φ.eval ρ⌝ -∗ Assertion.pre W Φ ke ρ)))

def Assertion.post (W : TinyML.World) {α} (Φ : α → Env → iProp) (m : Assertion TinyML.Typ α) (ρ : Env) : iProp :=
  match m with
  | .ret a        => Φ a ρ
  | .assert φ k   => ⌜φ.eval ρ⌝ -∗ Assertion.post W Φ k ρ
  | .let_ x t k   => let v := t.eval ρ; Assertion.post W Φ k (ρ.updateConst x.sort x.name v)
  | .pred x p k   => iprop(∀ (v : x.sort.denote),
      p.eval W ρ v -∗ Assertion.post W Φ k (ρ.updateConst x.sort x.name v))
  | .ite φ kt ke  =>
      iprop((⌜φ.eval ρ⌝ -∗ Assertion.post W Φ kt ρ) ∧
            (⌜¬ φ.eval ρ⌝ -∗ Assertion.post W Φ ke ρ))

-- ---------------------------------------------------------------------------
-- Predicate transformers
-- ---------------------------------------------------------------------------

def PredTrans.apply (W : TinyML.World) (Φ : Runtime.Val → iProp) (m : PredTrans TinyML.Typ) (ρ : Env) : iProp :=
  Assertion.pre W (fun post ρ' =>
    BIBase.forall fun v : Runtime.Val =>
      Assertion.post W (fun () _ => Φ v) post.body (ρ'.updateConst .value post.name v)
  ) m ρ

-- ---------------------------------------------------------------------------
-- Specifications
-- ---------------------------------------------------------------------------

namespace Spec

/-- Build an environment binding each argument name to its value, left-to-right.
    Later arguments shadow earlier ones with the same name. -/
def argsEnv (ρ : Env) : List String → List Runtime.Val → Env
  | [], _ | _, [] => ρ
  | name :: rest, v :: vs => argsEnv (ρ.updateConst .value name v) rest vs

def isPrecondFor (W : TinyML.World)
    (argTys : List TinyML.Typ) (retTy : TinyML.Typ)
    (f : Runtime.Val) (s : Spec TinyML.Typ) : iProp :=
  iprop(□ ∀ (ρ : Env) (Φ : Runtime.Val → iProp) (vs : List Runtime.Val),
      ⌜Env.agreeOn W.Δ_spec W.ρ_spec ρ⌝ -∗
      TinyML.ValsHaveTypes W vs argTys -∗
        PredTrans.apply W (fun r => TinyML.ValHasType W r retTy -∗ Φ r) s.pred
          (argsEnv ρ s.args vs) -∗
        wp W.pctx (Runtime.Expr.app (.val f) (vs.map fun v => .val v)) Φ)

instance : Iris.BI.Persistent (isPrecondFor W argTys retTy f s) := by
  unfold isPrecondFor
  infer_instance

end Spec

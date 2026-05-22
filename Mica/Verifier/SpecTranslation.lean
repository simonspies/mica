-- SUMMARY: Translation from typechecked frontend specifications into verifier assertions and predicate transformers.
import Mica.TinyML.Spec
import Mica.FOL.Printing
import Mica.Verifier.Assertions
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.RelationalEncoding

/-!
# Spec Translation

Translates a typechecked `Spec.Body` into `Assertion`/`PredTrans` values.
Leaf expressions are encoded into FOL via `encodeWith Skolemize.encoderOps`,
producing a `DefVal` (a value term and its definedness condition). Each
definedness obligation is asserted before the value it guards is bound or
tested.
-/

namespace SpecTranslation

open Verifier.RelationalEncoding

private abbrev M := Except String

/-- Encode a spec expression into a `DefVal`. -/
def encodeExpr (Γfn : FunCtx) (δ : VarEnv) (e : Typed.Expr) : M Skolemize.DefVal :=
  encodeWith Skolemize.encoderOps Γfn δ e (fun v => .ok (Skolemize.DefVal.pure v))

/-- Encode a boolean spec expression into its definedness and truth formulas. -/
def encodeBool (Γfn : FunCtx) (δ : VarEnv) (e : Typed.Expr) : M (Formula × Formula) := do
  let dv ← encodeExpr Γfn δ e
  .ok (dv.defined, .eq .bool (.unop .toBool dv.value) (.const (.b true)))

/-- Look up a spec-level variable's encoded value. -/
private def lookupVar (δ : VarEnv) (x : String) : M (Term .value) :=
  match δ.lookup x with
  | some v => .ok v
  | none => .error s!"unbound spec variable '{x}'"

/-- Assert all formulas in order before continuing with the assertion body. -/
private def assertAll (φs : List Formula) (k : Assertion α) : Assertion α :=
  φs.foldr .assert k

/-- Translate a predicate into an atom over its looked-up scrutinee. -/
def translatePred (δ : VarEnv) (ty : TinyML.Typ) : Spec.Pred → M (Atom .value)
  | .isinj tag arity scrut => do .ok (.isinj tag arity (← lookupVar δ scrut))
  | .own loc => do .ok (.own (← lookupVar δ loc) ty)

/-- Translate a spec assertion, asserting each leaf's definedness before its value. -/
def translateAssert (Γfn : FunCtx) (inner : VarEnv → α → M β) :
    VarEnv → Spec.Assert Typed.Expr α → M (Assertion β)
  | δ, .ret a => do .ok (.ret (← inner δ a))
  | δ, .assert cond rest => do
    let (defd, φ) ← encodeBool Γfn δ cond
    .ok (.assert defd (.assert φ (← translateAssert Γfn inner δ rest)))
  | δ, .let_ x e rest => do
    let dv ← encodeExpr Γfn δ e
    let v : Var := ⟨x, .value⟩
    .ok (.assert dv.defined (.let_ v dv.value
      (assertAll (TinyML.typeConstraints e.ty (.var .value x))
        (← translateAssert Γfn inner (δ.bind x (.var .value x)) rest))))
  | δ, .bind pred x ty rest => do
    let atom ← translatePred δ ty pred
    let v : Var := ⟨x, .value⟩
    .ok (.pred v atom
      (assertAll (TinyML.typeConstraints ty (.var .value x))
        (← translateAssert Γfn inner (δ.bind x (.var .value x)) rest)))
  | δ, .ite cond thn els => do
    let (defd, φ) ← encodeBool Γfn δ cond
    .ok (.assert defd (.ite φ (← translateAssert Γfn inner δ thn)
      (← translateAssert Γfn inner δ els)))

def translatePost (Γfn : FunCtx) (δ : VarEnv) : Spec.Post Typed.Expr → M (Assertion Unit) :=
  translateAssert Γfn (fun _ () => .ok ()) δ

def translatePre (Γfn : FunCtx) (δ : VarEnv) : Spec.Pre Typed.Expr → M PredTrans :=
  translateAssert Γfn (fun δ (name, post) => do
    let post' ← translatePost Γfn (δ.bind name (.var .value name)) post
    .ok (name, post')) δ

/-- Build the initial encoder environment from the spec's argument names. -/
private def argEnv (names : List String) : VarEnv :=
  names.map (fun n => (n, .var .value n))

/-- Translate a typechecked spec body into a spec predicate. -/
def translate (Γfn : FunCtx) (body : (Spec.Body Typed.Expr)) : M SpecPredicate :=
  let (names, pre) := body
  do
    let pt ← translatePre Γfn (argEnv names) pre
    .ok (names, pt)

end SpecTranslation

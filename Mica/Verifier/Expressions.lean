-- SUMMARY: Compilation of typed TinyML expressions into verifier terms, with weakest-precondition correctness proofs.
import Mica.TinyML.Typed
import Mica.TinyML.Typing
import Mica.TinyML.OpSem
import Mica.SeparationLogic.PrimitiveLaws
import Mica.Verifier.Utils
import Mica.Verifier.Monad
import Mica.Verifier.Assertions
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.Specifications
import Mica.Verifier.SpecMaps
import Mica.Engine.Driver
import Mica.Base.Fresh
import Mathlib.Data.Finmap
import Mica.Verifier.Intrinsic

open Iris Iris.BI
open Typed

/-! ## Expression Compilation

Compiles TinyML expressions to SMT terms via `VerifM`, lifting primitive operations
to the FOL term language. Correctness is stated against the weakest-precondition calculus. -/

/-! ### Operation semantics and SMT translation -/

/-- Lift a `TinyML.BinOp` to operate on `Term .value`, using `toInt`/`toBool`/`ofInt`/`ofBool`.
    Returns `none` for ops that are not (yet) supported. -/
def compileOp (op : TinyML.BinOp) (sl sr : Term .value) : Option (Term .value) :=
  let i t := Term.unop UnOp.toInt  t
  let b t := Term.unop UnOp.toBool t
  match op with
  | .add  => some (Term.unop .ofInt  (Term.binop .add  (i sl) (i sr)))
  | .sub  => some (Term.unop .ofInt  (Term.binop .sub  (i sl) (i sr)))
  | .mul  => some (Term.unop .ofInt  (Term.binop .mul  (i sl) (i sr)))
  -- Division and modulo are handled directly in `compile` with a non-zero divisor
  -- assertion, so they do not go through `compileOp`.
  | .div  => none
  | .mod  => none
  | .eq   => some (Term.unop .ofBool (Term.binop .eq   (i sl) (i sr)))
  | .lt   => some (Term.unop .ofBool (Term.binop .less (i sl) (i sr)))
  | .le   => some (Term.unop .ofBool (Term.binop .ge   (i sr) (i sl)))
  | .gt   => some (Term.unop .ofBool (Term.binop .gt   (i sl) (i sr)))
  | .ge   => some (Term.unop .ofBool (Term.binop .ge   (i sl) (i sr)))
  | .and  => some (Term.unop .ofBool (Term.ite (b sl) (b sr) (.const (.b false))))
  | .or   => some (Term.unop .ofBool (Term.ite (b sl) (.const (.b true)) (b sr)))

def compileUnop (op : TinyML.UnOp) (s : Term .value) : Option (Term .value) :=
  let i t := Term.unop UnOp.toInt  t
  let b t := Term.unop UnOp.toBool t
  match op with
  | .neg => some (Term.unop .ofInt  (Term.unop .neg (i s)))
  | .not => some (Term.unop .ofBool (Term.unop .not (b s)))
  | .proj n => some (.unop .vhead (vtailN (.unop .toValList s) n))

theorem compileUnop_wfIn {op : TinyML.UnOp} {s : Term .value} {Δ : Signature}
    (hs : s.wfIn Δ) {t : Term .value} (heq : compileUnop op s = some t) :
    t.wfIn Δ := by
  cases op <;> simp [compileUnop] at heq <;> subst heq <;>
    simp only [Term.wfIn, UnOp.wfIn, true_and]
  all_goals first | exact hs | (have : (Term.unop UnOp.toValList s).wfIn _ := ⟨trivial, hs⟩; exact vtailN_wfIn this _)

theorem compileUnop_eval {op : TinyML.UnOp} {s : Term .value} {ρ : VerifM.Env}
    {v w : Runtime.Val} {t : Term .value}
    (hs : s.eval ρ.env = v) (heval : TinyML.evalUnOp op v = some w)
    (hcomp : compileUnop op s = some t) :
    t.eval ρ.env = w := by
  subst hs
  cases op with
  | proj n =>
    simp only [compileUnop, Option.some.injEq] at hcomp; subst hcomp
    cases h : s.eval ρ.env <;> simp_all [TinyML.evalUnOp]
    exact vhead_vtailN_eval heval _ ρ.env (by simp [Term.eval, UnOp.eval, h])
  | neg | not =>
    simp only [compileUnop, Option.some.injEq] at hcomp
    subst hcomp
    cases h : s.eval ρ.env <;>
    simp_all [TinyML.evalUnOp, Term.eval, UnOp.eval]

theorem compileOp_wfIn {op : TinyML.BinOp} {sl sr : Term .value} {Δ : Signature}
    (hl : sl.wfIn Δ) (hr : sr.wfIn Δ) {t : Term .value} (heq : compileOp op sl sr = some t) :
    t.wfIn Δ := by
  cases op <;> simp [compileOp] at heq <;> subst heq <;>
    simp only [Term.wfIn] <;>
    tauto

/-- If `evalBinOp op v1 v2 = some w` and the input terms evaluate to `v1`, `v2`,
    then the compiled SMT term evaluates to `w`.
    Pair/store return `none` from `compileOp` so those cases are vacuous via `hcomp`. -/
theorem compileOp_eval {op : TinyML.BinOp} {sl sr : Term .value} {ρ : VerifM.Env}
    {v1 v2 w : Runtime.Val} {t : Term .value}
    (hsl : sl.eval ρ.env = v1) (hsr : sr.eval ρ.env = v2)
    (heval : TinyML.evalBinOp op v1 v2 = some w)
    (hcomp : compileOp op sl sr = some t) :
    t.eval ρ.env = w := by
  subst hsl hsr
  cases op <;>
    simp only [compileOp, Option.some.injEq] at hcomp <;>
    (try simp at hcomp) <;>
    subst hcomp <;>
    (cases h1 : sl.eval ρ.env <;> cases h2 : sr.eval ρ.env) <;>
    simp_all [TinyML.evalBinOp, Term.eval, UnOp.eval, BinOp.eval, Const.denote,
              Bool.cond_eq_ite, ge_iff_le, Bool.beq_eq_decide_eq]


/-! ### Compiler and Top-Level Verifier -/

mutual
  def compile (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) : Expr → VerifM (Term .value)
    | .const (.int n)  => pure (.unop .ofInt  (.const (.i n)))
    | .const (.bool b) => pure (.unop .ofBool (.const (.b b)))
    | .const .unit     => pure (Term.const .unit)
    | .var x vty => do
        let x' ← VerifM.expectSome s!"undefined variable: {x}" (B.lookup x)
        VerifM.expectEq s!"type annotation mismatch for variable: {x}" (Γ x |>.getD .value) vty
        pure (.const (.uninterpreted x'.name .value))
    | .unop op e uty => do
        let se ← compile reg Θ Δ_spec S B Γ e
        let ty ← VerifM.expectSome
          s!"type error: operator {repr op} cannot be applied to {repr e.ty}"
          (TinyML.UnOp.typeOf op e.ty)
        VerifM.expectEq "unop type annotation mismatch" ty uty
        let t ← VerifM.expectSome
          s!"unsupported unary operator: {repr op}"
          (compileUnop op se)
        pure t
    | .assert e => do
        let sl ← compile reg Θ Δ_spec S B Γ e
        VerifM.assert (Formula.eq .bool (Term.unop .toBool sl) (Term.const (.b true)))
        pure (Term.const .unit)
    | .binop op l r bty => do
        let sr ← compile reg Θ Δ_spec S B Γ r
        let sl ← compile reg Θ Δ_spec S B Γ l
        let ty ← VerifM.expectSome
          s!"type error: operator {repr op} cannot be applied to {repr l.ty} and {repr r.ty}"
          (TinyML.BinOp.typeOf op l.ty r.ty)
        VerifM.expectEq "binop type annotation mismatch" ty bty
        if op = .div ∨ op = .mod then do
          let i t := Term.unop UnOp.toInt t
          let fol_op := if op == .div then BinOp.div else BinOp.mod
          VerifM.assert (.not (.eq .int (i sr) (.const (.i 0))))
          pure (Term.unop .ofInt (Term.binop fol_op (i sl) (i sr)))
        else do
          let t ← VerifM.expectSome
            s!"unsupported binary operator: {repr op}"
            (compileOp op sl sr)
          pure t
    | .letIn b e body => do
        let se ← compile reg Θ Δ_spec S B Γ e
        VerifM.expectEq "let type annotation mismatch" b.ty e.ty
        match b.name with
        | none => compile reg Θ Δ_spec S B Γ body
        | some x =>
          let x' ← VerifM.decl (some x) .value
          VerifM.assume (.pure (Formula.eq .value (.const (.uninterpreted x'.name .value)) se))
          compile reg Θ Δ_spec (Finmap.erase x S) ((x, x') :: B) (Γ.extend x e.ty) body
    | .ifThenElse cond thn els ty => do
        let sc ← compile reg Θ Δ_spec S B Γ cond
        VerifM.expectEq "if condition type mismatch" cond.ty .bool
        VerifM.expectEq "if branch type annotation mismatch" thn.ty ty
        VerifM.expectEq "if branch type annotation mismatch" els.ty ty
        let branch ← VerifM.all [true, false]
        if branch then do
          VerifM.assume (.pure (.not (.eq .value sc (.unop .ofBool (.const (.b false))))))
          compile reg Θ Δ_spec S B Γ thn
        else do
          VerifM.assume (.pure (.eq .value sc (.unop .ofBool (.const (.b false)))))
          compile reg Θ Δ_spec S B Γ els
    | .app (.var f fty) args aty => do
        let spec ← VerifM.expectSome s!"no spec for function {f}" (S.lookup f)
        let sterms ← compileExprs reg Θ Δ_spec S B Γ args
        let sargs := (args.map Expr.ty).zip sterms
        VerifM.expectEq "app type annotation mismatch" spec.retTy aty
        VerifM.expectEq "app type annotation mismatch"
          fty (Typed.arrowOfArgs (spec.args.map fun arg => Binder.named arg.1 arg.2) spec.retTy)
        let (_, result) ← Spec.call Θ (FiniteSubst.base Δ_spec) spec sargs
        pure result
    | .app (.prim n _) args aty => do
        let i ← VerifM.expectSome s!"unknown primitive `{n}`"
          (reg.lookup? n)
        let spec := i.spec
        VerifM.expectEq "primitive return type mismatch" i.resultTy aty
        let sterms ← compileExprs reg Θ Δ_spec S B Γ args
        let sargs := (args.map Expr.ty).zip sterms
        let (_, result) ← Spec.call Θ (FiniteSubst.base Δ_spec) spec sargs
        pure result
    | .prim n _ => VerifM.fatal s!"primitive `{n}` must be applied"
    | .tuple es => do
        let terms ← compileExprs reg Θ Δ_spec S B Γ es
        pure (.unop .ofValList (Terms.toValList terms))
    | .inj tag arity payload => do
        if tag ≥ arity then VerifM.fatal "inj tag out of range"
        else
          let s ← compile reg Θ Δ_spec S B Γ payload
          pure (.unop (.mkInj tag arity) s)
    | .match_ scrut branches ty => do
        let sc ← compile reg Θ Δ_spec S B Γ scrut
        match scrut.ty with
        | .sum ts =>
          if ts.length ≠ branches.length then VerifM.fatal "match arity mismatch"
          else if ∀ br ∈ branches, br.2.ty = ty then do
            let actions := compileBranches reg Θ Δ_spec S B Γ sc ts branches 0
            let i ← VerifM.all (List.range actions.length)
            match actions[i]? with
            | some m => m
            | none => VerifM.fatal "match branch index out of range"
          else
            VerifM.fatal "match branch type annotation mismatch"
        | _ => VerifM.fatal "match on non-sum type"
    | .cast e ty => do
        let se ← compile reg Θ Δ_spec S B Γ e
        if TinyML.Typ.sub Θ e.ty ty then pure se
        else VerifM.fatal s!"cast type mismatch"
    | .ref false e => do
        let _ ← compile reg Θ Δ_spec S B Γ e
        let l ← VerifM.decl none .value
        pure (.const (.uninterpreted l.name .value))
    | .ref true e => do
        let v ← compile reg Θ Δ_spec S B Γ e
        let l ← VerifM.decl none .value
        let sl := Term.const (.uninterpreted l.name .value)
        VerifM.assume (.spatial (.pointsTo sl v e.ty))
        pure sl
    | .deref e ty => do
        match e.ty with
        | .owned ty' => do
            VerifM.expectEq "deref type annotation mismatch" ty' ty
            let lq ← compile reg Θ Δ_spec S B Γ e
            let v ← VerifM.findMatchForce lq ty
            VerifM.assume (.spatial (.pointsTo lq v ty))
            pure v
        | .ref ty' => do
            VerifM.expectEq "deref type annotation mismatch" ty' ty
            let _ ← compile reg Θ Δ_spec S B Γ e
            let v ← VerifM.decl none .value
            let sv := Term.const (.uninterpreted v.name .value)
            VerifM.assumeAll (TinyML.typeConstraints ty sv)
            pure sv
        | _ => VerifM.fatal "deref operand is not a reference"
    | .store loc val => do
        match loc.ty with
        | .owned ty => do
            VerifM.expectEq "store location type mismatch" ty val.ty
            let v ← compile reg Θ Δ_spec S B Γ val
            let lq ← compile reg Θ Δ_spec S B Γ loc
            let _ ← VerifM.findMatchForce lq val.ty
            VerifM.assume (.spatial (.pointsTo lq v val.ty))
            pure (Term.const .unit)
        | .ref ty => do
            VerifM.expectEq "store location type mismatch" ty val.ty
            let _ ← compile reg Θ Δ_spec S B Γ val
            let _ ← compile reg Θ Δ_spec S B Γ loc
            pure (Term.const .unit)
        | _ => VerifM.fatal "store location is not a reference"
    | .app _ _ _ | .fix _ _ _ _ => VerifM.fatal "unsupported expression"

  /-- Compile a single match branch: assume the scrutinee is `mkInj i n payload`, then compile the body. -/
  def compileBranch (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
      (sc : Term .value) (n : Nat) (i : Nat) (ty_i : TinyML.Typ)
      : Binder × Expr → VerifM (Term .value)
    | (binder, body) => do
        VerifM.expectEq "match binder type annotation mismatch" binder.ty ty_i
        let xv ← VerifM.decl binder.name .value
        VerifM.assume (.pure (.eq .value sc (.unop (.mkInj i n) (.const (.uninterpreted xv.name .value)))))
        VerifM.assumeAll (TinyML.typeConstraints ty_i (.const (.uninterpreted xv.name .value)))
        match binder.name with
        | some x =>
          compile reg Θ Δ_spec (Finmap.erase x S) ((x, xv) :: B) (Γ.extendBinder binder ty_i) body
        | none =>
          compile reg Θ Δ_spec S B (Γ.extendBinder binder ty_i) body

  def compileBranches (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
      (sc : Term .value) (ts : List TinyML.Typ) :
      List (Binder × Expr) → Nat → List (VerifM (Term .value))
    | [], _ => []
    | branch :: rest, i =>
      compileBranch reg Θ Δ_spec S B Γ sc ts.length i (ts[i]?.getD .value) branch
        :: compileBranches reg Θ Δ_spec S B Γ sc ts rest (i + 1)

  def compileExprs (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) : List Expr → VerifM (List (Term .value))
    | [] => pure []
    | e :: es => do
      let rest ← compileExprs reg Θ Δ_spec S B Γ es
      let se ← compile reg Θ Δ_spec S B Γ e
      pure (se :: rest)
end

/-! ### Helper lemmas -/

theorem compileBranches_length_get (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (sc : Term .value) (ts : List TinyML.Typ)
    (branches : List (Binder × Expr)) (idx : Nat) :
    (compileBranches reg Θ Δ_spec S B Γ sc ts branches idx).length = branches.length ∧
    ∀ j, j < branches.length →
      (compileBranches reg Θ Δ_spec S B Γ sc ts branches idx)[j]? =
        branches[j]?.map (fun branch => compileBranch reg Θ Δ_spec S B Γ sc ts.length (idx + j) (ts[idx + j]?.getD .value) branch) := by
  induction branches generalizing idx with
  | nil => exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | cons b bs ih =>
    have ⟨ih_len, ih_get⟩ := ih (idx + 1)
    constructor
    · simp [compileBranches, ih_len]
    · intro j hj
      cases j with
      | zero => simp [compileBranches]
      | succ k =>
        simp [compileBranches]
        have hk : k < bs.length := Nat.lt_of_succ_lt_succ hj
        have : idx + 1 + k = idx + (k + 1) := by omega
        rw [ih_get k hk, this]

namespace Helpers

theorem ctx_dup (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (st : TransState) (ρ : VerifM.Env) (γ : Runtime.Subst) (R : iProp) :
    st.sl Θ ρ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗ R) ⊢
      st.sl Θ ρ ∗
        (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗
          (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗ R)) := by
  iintro ⟨Howns, □HS, □HT, HR⟩
  isplitl [Howns]
  · iexact Howns
  · isplitl []
    · iexact HS
    · isplitl []
      · iexact HT
      · isplitl []
        · iexact HS
        · isplitl []
          · iexact HT
          · iexact HR

theorem ctx_dup_flip (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (st : TransState) (ρ : VerifM.Env) (γ : Runtime.Subst) (R : iProp) :
    st.sl Θ ρ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗ R) ⊢
      st.sl Θ ρ ∗
        (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗
          (B.typedSubst Θ Γ γ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R))) := by
  iintro ⟨Howns, □HS, □HT, HR⟩
  isplitl [Howns]
  · iexact Howns
  · isplitl []
    · iexact HS
    · isplitl []
      · iexact HT
      · isplitl []
        · iexact HT
        · isplitl []
          · iexact HS
          · iexact HR

theorem ctx_push (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (st : TransState) (ρ : VerifM.Env) (γ : Runtime.Subst) (R : iProp)
    (v : Runtime.Val) (ty : TinyML.Typ) :
    st.sl Θ ρ ∗ TinyML.ValHasType Θ v ty ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗ R) ⊢
      st.sl Θ ρ ∗
        (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗
          (TinyML.ValHasType Θ v ty ∗ R)) := by
  iintro ⟨Howns, Hv, □HS, □HT, HR⟩
  isplitl [Howns]
  · iexact Howns
  · isplitl []
    · iexact HS
    · isplitl []
      · iexact HT
      · isplitl [Hv]
        · iexact Hv
        · iexact HR

theorem ctx_push_flip (reg : Verifier.Registry) (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (st : TransState) (ρ : VerifM.Env) (γ : Runtime.Subst) (R : iProp)
    (v : Runtime.Val) (ty : TinyML.Typ) :
    st.sl Θ ρ ∗ TinyML.ValHasType Θ v ty ∗ (B.typedSubst Θ Γ γ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R)) ⊢
      st.sl Θ ρ ∗
        (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗
          (TinyML.ValHasType Θ v ty ∗ R)) := by
  iintro ⟨Howns, Hv, □HT, □HS, HR⟩
  isplitl [Howns]
  · iexact Howns
  · isplitl []
    · iexact HS
    · isplitl []
      · iexact HT
      · isplitl [Hv]
        · iexact Hv
        · iexact HR

end Helpers


/-! ### Correctness -/

/-! #### Correctness Statements -/

private theorem specInvariants_mono
    {Δ_spec : Signature} {ρ_spec st st' : VerifM.Env} {decls decls' : Signature}
    (hΔspec : Δ_spec.Subset decls)
    (hρspec : VerifM.Env.agreeOn Δ_spec ρ_spec st)
    (hdecls : decls.Subset decls')
    (hagree : VerifM.Env.agreeOn decls st st') :
    Δ_spec.Subset decls' ∧ VerifM.Env.agreeOn Δ_spec ρ_spec st' := by
  refine ⟨hΔspec.trans hdecls, VerifM.Env.agreeOn_trans hρspec ?_⟩
  exact VerifM.Env.agreeOn_mono hΔspec hagree

def correctExpr (reg : Verifier.Registry) (e : Expr) : Prop :=
  ∀ (Θ : TinyML.TypeEnv) (R : iProp) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) (st : TransState) (ρ : VerifM.Env) (γ : Runtime.Subst)
  (Δ_spec : Signature) (ρ_spec : VerifM.Env)
  (Ψ : Term .value → TransState → VerifM.Env → Prop) (Φ : Runtime.Val → iProp),
    VerifM.eval (compile reg Θ Δ_spec S B Γ e) st ρ Ψ →
    B.agreeOnLinked ρ.env γ →
    B.wfIn st.decls →
    S.wfIn Δ_spec →
    Δ_spec.wf →
    Δ_spec.vars = [] →
    Δ_spec.Subset st.decls →
    VerifM.Env.agreeOn Δ_spec ρ_spec ρ →
    Verifier.Registry.symSubset reg Δ_spec →
    Verifier.Registry.symAgree reg ρ_spec.env →
    (∀ v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls → Term.eval ρ'.env se = v →
      st'.sl Θ ρ' ∗ TinyML.ValHasType Θ v e.ty ∗ R ⊢ Φ v) →
    st.sl Θ ρ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗ R) ⊢ wp (reg.wpCtx) (e.runtime.subst γ) Φ

def correctBranch (reg : Verifier.Registry) (branch : Binder × Expr) : Prop :=
  ∀ (Θ : TinyML.TypeEnv) (R : iProp) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (sc : Term .value) (n i : Nat) (ty_i : TinyML.Typ)
    (st : TransState) (ρ : VerifM.Env) (γ : Runtime.Subst)
    (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (Ψ : Term .value → TransState → VerifM.Env → Prop)
    (Φ : Runtime.Val → iProp),
    VerifM.eval (compileBranch reg Θ Δ_spec S B Γ sc n i ty_i branch) st ρ Ψ →
    B.agreeOnLinked ρ.env γ →
    B.wfIn st.decls →
    S.wfIn Δ_spec →
    Δ_spec.wf →
    Δ_spec.vars = [] →
    Δ_spec.Subset st.decls →
    VerifM.Env.agreeOn Δ_spec ρ_spec ρ →
    Verifier.Registry.symSubset reg Δ_spec →
    Verifier.Registry.symAgree reg ρ_spec.env →
    sc.wfIn st.decls →
    (∀ v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls →
      se.eval ρ'.env = v → st'.sl Θ ρ' ∗ TinyML.ValHasType Θ v branch.2.ty ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R) ⊢ Φ v) →
    ∀ payload, sc.eval ρ.env = Runtime.Val.inj i n payload →
      st.sl Θ ρ ∗ TinyML.ValHasType Θ payload ty_i ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗ R) ⊢ wp (reg.wpCtx) (.app ((Runtime.Expr.fix .none [branch.1.runtime] branch.2.runtime).subst γ) [.val payload]) Φ

def correctBranches (reg : Verifier.Registry) (branches : List (Binder × Expr)) : Prop :=
  ∀ (Θ : TinyML.TypeEnv) (R : iProp) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (sc : Term .value) (n : Nat) (ts : List TinyML.Typ) (idx : Nat)
    (st : TransState) (ρ : VerifM.Env) (γ : Runtime.Subst)
    (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (Ψ : Term .value → TransState → VerifM.Env → Prop)
    (Φ : Runtime.Val → iProp),
    B.agreeOnLinked ρ.env γ →
    B.wfIn st.decls →
    S.wfIn Δ_spec →
    Δ_spec.wf →
    Δ_spec.vars = [] →
    Δ_spec.Subset st.decls →
    VerifM.Env.agreeOn Δ_spec ρ_spec ρ →
    Verifier.Registry.symSubset reg Δ_spec →
    Verifier.Registry.symAgree reg ρ_spec.env →
    sc.wfIn st.decls →
    (∀ (j : Nat) (hj : j < branches.length) v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls →
      se.eval ρ'.env = v → st'.sl Θ ρ' ∗ TinyML.ValHasType Θ v (branches[j]).2.ty ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R) ⊢ Φ v) →
    ∀ (j : Nat) (hj : j < branches.length),
      VerifM.eval (compileBranch reg Θ Δ_spec S B Γ sc n (idx + j) (ts[idx + j]?.getD .value) branches[j]) st ρ Ψ →
      ∀ payload, sc.eval ρ.env = Runtime.Val.inj (idx + j) n payload →
        st.sl Θ ρ ∗ TinyML.ValHasType Θ payload (ts[idx + j]?.getD .value) ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗ R) ⊢ wp (reg.wpCtx) (.app ((Runtime.Expr.fix .none [(branches[j]).1.runtime] (branches[j]).2.runtime).subst γ) [.val payload]) Φ

def correctExprs (reg : Verifier.Registry) (es : List Expr) : Prop :=
  ∀ (Θ : TinyML.TypeEnv) (R : iProp) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (st : TransState) (ρ : VerifM.Env) (γ : Runtime.Subst)
    (Δ_spec : Signature) (ρ_spec : VerifM.Env)
    (Ψ : List (Term .value) → TransState → VerifM.Env → Prop)
    (Φ : List Runtime.Val → iProp),
    VerifM.eval (compileExprs reg Θ Δ_spec S B Γ es) st ρ Ψ →
    B.agreeOnLinked ρ.env γ →
    B.wfIn st.decls →
    S.wfIn Δ_spec →
    Δ_spec.wf →
    Δ_spec.vars = [] →
    Δ_spec.Subset st.decls →
    VerifM.Env.agreeOn Δ_spec ρ_spec ρ →
    Verifier.Registry.symSubset reg Δ_spec →
    Verifier.Registry.symAgree reg ρ_spec.env →
    (∀ vs ρ' st' terms, Ψ terms st' ρ' →
      (∀ t ∈ terms, t.wfIn st'.decls) →
      Terms.Eval ρ'.env terms vs →
       st'.sl Θ ρ' ∗ TinyML.ValsHaveTypes Θ vs (es.map Expr.ty) ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R) ⊢ Φ vs) →
    st.sl Θ ρ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗ R) ⊢ wps (reg.wpCtx) (es.map (fun e => e.runtime.subst γ)) Φ

/-! #### Correctness Compatibility Lemmas -/

theorem compileConst_correct (reg : Verifier.Registry) (c : TinyML.Const) :
    correctExpr reg (.const c) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval _hagree _hbwf _hSwf _hΔwf _hΔvars _hΔspec _hρspec hΔreg hρreg hpost
  cases c with
  | int n =>
    simp only [compile] at heval
    simp only [Expr.runtime, Runtime.Val.ofConst, Runtime.Expr.subst_val]
    obtain heval := VerifM.eval_ret heval
    simp only [Expr.ty, Const.ty] at hpost
    refine SpatialContext.wp_val ?_
    istart
    iintro ⟨Howns, _HS, _Hts, HR⟩
    iapply (hpost (.int n) ρ st _ heval
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.denote]))
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · exact TinyML.ValHasType.int_intro Θ n
      · iexact HR
  | bool b =>
    simp only [compile] at heval
    simp only [Expr.runtime, Runtime.Val.ofConst, Runtime.Expr.subst_val]
    obtain heval := VerifM.eval_ret heval
    simp only [Expr.ty, Const.ty] at hpost
    refine SpatialContext.wp_val ?_
    istart
    iintro ⟨Howns, _HS, _Hts, HR⟩
    iapply (hpost (.bool b) ρ st _ heval
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.denote]))
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · exact TinyML.ValHasType.bool_intro Θ b
      · iexact HR
  | unit =>
    simp only [compile] at heval
    simp only [Expr.runtime, Runtime.Val.ofConst, Runtime.Expr.subst_val]
    obtain heval := VerifM.eval_ret heval
    simp only [Expr.ty, Const.ty] at hpost
    refine SpatialContext.wp_val ?_
    istart
    iintro ⟨Howns, _HS, _Hts, HR⟩
    iapply (hpost .unit ρ st _ heval
      (by simp [Term.wfIn, Const.wfIn])
      (by simp [Term.eval]))
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · exact TinyML.ValHasType.unit_intro Θ
      · iexact HR

theorem compileVar_correct (reg : Verifier.Registry) (x : String) (vty : TinyML.Typ) :
    correctExpr reg (.var x vty) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf _hSwf _hΔwf _hΔvars _hΔspec _hρspec hΔreg hρreg hpost
  simp only [compile] at heval
  obtain ⟨x', hbind, heval⟩ := VerifM.eval_bind_expectSome heval
  obtain ⟨hcheck, hcont⟩ := VerifM.eval_bind_expectEq heval
  unfold Expr.runtime
  simp only [Runtime.Expr.subst]
  obtain ⟨hsort, hγ⟩ := hagree x x' hbind
  rw [hγ]
  simp
  have hmem : (x, x') ∈ B := by
    obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hbind
    rw [heq]
    simp
  have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
  have hΨ : Ψ (Term.const (.uninterpreted x'.name .value)) st ρ := VerifM.eval_ret hcont
  have hwfv : (Term.const (.uninterpreted x'.name .value)).wfIn st.decls := by
    have h := hbwf _ hmem
    cases x' with
    | mk n s =>
      simp only at hsort; subst hsort
      exact Term.const_wfIn_of_mem hwfst h
  have htyped {t : TinyML.Typ} (hΓ : Γ x = some t) :
      B.typedSubst Θ Γ γ ⊢ TinyML.ValHasType Θ (ρ.env.consts .value x'.name) t := by
    unfold Bindings.typedSubst
    iintro □Hts
    ispecialize Hts $$ %x %x' %t %hbind %hΓ
    icases Hts with ⟨%v, %hγv, Hvty⟩
    have hv : v = ρ.env.consts .value x'.name := by
      rw [hγ] at hγv
      exact Option.some.inj hγv.symm
    subst hv
    iexact Hvty
  simp only [Expr.ty] at hpost
  cases hΓx : Γ x with
  | none =>
    have hvty : vty = .value := by simpa [hΓx] using hcheck.symm
    subst hvty
    have hvalue : ⊢ TinyML.ValHasType Θ (ρ.env.consts .value x'.name) .value := by
      iapply (TinyML.ValHasType.value Θ (ρ.env.consts .value x'.name)).2
      ipure_intro
      trivial
    have hprep :
        st.sl Θ ρ ∗ (B.typedSubst Θ Γ γ ∗ R) ⊢
          st.sl Θ ρ ∗ TinyML.ValHasType Θ (ρ.env.consts .value x'.name) .value ∗ R := by
      exact sep_mono_r (sep_mono_l (true_intro.trans hvalue))
    have hpost' :
        st.sl Θ ρ ∗ TinyML.ValHasType Θ (ρ.env.consts .value x'.name) .value ∗ R ⊢
          Φ (ρ.env.consts .value x'.name) := by
      simpa [hΓx] using
        (hpost (ρ.env.consts .value x'.name) ρ st (Term.const (.uninterpreted x'.name .value))
          hΨ hwfv (by simp [Term.eval, Const.denote]))
    exact SpatialContext.wp_val <| (sep_mono_r sep_elim_r).trans <| hprep.trans <| hpost'
  | some t =>
    have hΓ : Γ x = some t := hΓx
    have htv : t = vty := by simpa [hΓx] using hcheck
    have hprep :
        st.sl Θ ρ ∗ (B.typedSubst Θ Γ γ ∗ R) ⊢
          st.sl Θ ρ ∗ TinyML.ValHasType Θ (ρ.env.consts .value x'.name) vty ∗ R := by
      rw [← htv]
      exact sep_mono_r (sep_mono_l (htyped hΓ))
    have hpost' :
        st.sl Θ ρ ∗ TinyML.ValHasType Θ (ρ.env.consts .value x'.name) vty ∗ R ⊢
          Φ (ρ.env.consts .value x'.name) :=
      hpost (ρ.env.consts .value x'.name) ρ st (Term.const (.uninterpreted x'.name .value))
        hΨ hwfv (by simp [Term.eval, Const.denote])
    exact SpatialContext.wp_val <| (sep_mono_r sep_elim_r).trans <| hprep.trans <| hpost'

theorem compileInj_correct (reg : Verifier.Registry) (tag arity : Nat) (payload : Expr)
    (ihPayload : correctExpr reg payload) :
    correctExpr reg (.inj tag arity payload) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  by_cases htag : tag ≥ arity
  · simp [htag] at heval
    exact (VerifM.eval_fatal heval).elim
  · push_neg at htag
    simp [show ¬(tag ≥ arity) from Nat.not_le.mpr htag] at heval
    have heval_p : (compile reg Θ Δ_spec S B Γ payload).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine SpatialContext.wp_bind_inj <| ihPayload Θ R S B Γ st ρ γ Δ_spec ρ_spec _ _
      (VerifM.eval.decls_grow ρ heval_p) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
    intro v_p ρ_p st_p se_p hΨ_p hse_wf_p heval_se_p
    obtain ⟨_hdecls_p, _hagreeOn_p, hΨ_p⟩ := hΨ_p
    obtain hΨ_p := VerifM.eval_ret hΨ_p
    simp only [Expr.ty] at hpost
    let ts := (List.replicate arity TinyML.Typ.empty).set tag payload.ty
    have hlen_ts : ts.length = arity := by simp [ts]
    have hget_ts : ts[tag]? = some payload.ty := by simp [ts, htag]
    have hinj : TinyML.ValHasType Θ v_p payload.ty ⊢
        TinyML.ValHasType Θ (.inj tag arity v_p) (.sum ts) :=
      TinyML.ValHasType.inj hlen_ts hget_ts
    have hprep :
        st_p.sl Θ ρ_p ∗ TinyML.ValHasType Θ v_p payload.ty ∗ R ⊢
          st_p.sl Θ ρ_p ∗ TinyML.ValHasType Θ (.inj tag arity v_p) (.sum ts) ∗ R :=
      sep_mono_r (sep_mono_l hinj)
    have hpost' :
        st_p.sl Θ ρ_p ∗ TinyML.ValHasType Θ (.inj tag arity v_p) (.sum ts) ∗ R ⊢
          Φ (.inj tag arity v_p) := by
      simpa [ts, hlen_ts] using
        (hpost (.inj tag arity v_p) ρ_p st_p _ hΨ_p
          (by simp only [Term.wfIn]; exact ⟨trivial, hse_wf_p⟩)
          (by simp [Term.eval, UnOp.eval, heval_se_p]))
    exact SpatialContext.wp_inj <| hprep.trans hpost'

theorem compileCast_correct (reg : Verifier.Registry) (e : Expr) (ty : TinyML.Typ)
    (ih : correctExpr reg e) :
    correctExpr reg (.cast e ty) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  simp only [Expr.ty] at hpost
  simp only [compile] at heval
  have heval_e : (compile reg Θ Δ_spec S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  simp [Expr.runtime]
  refine ih Θ R S B Γ st ρ γ Δ_spec ρ_spec _ _ (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
  intro v ρ' st' se hΨ hse_wf heval_se
  obtain ⟨_, _, hΨ⟩ := hΨ
  cases hsub : TinyML.Typ.sub Θ e.ty ty with
  | false =>
    simp [hsub] at hΨ
    exact (VerifM.eval_fatal hΨ).elim
  | true =>
    simp [hsub] at hΨ
    obtain hΨ := VerifM.eval_ret hΨ
    have hsub' : TinyML.Typ.Sub Θ e.ty ty := TinyML.Typ.sub_sound hsub
    have hprep :
        st'.sl Θ ρ' ∗ TinyML.ValHasType Θ v e.ty ∗ R ⊢
          st'.sl Θ ρ' ∗ TinyML.ValHasType Θ v ty ∗ R :=
      sep_mono_r (sep_mono_l (TinyML.ValHasType.sub hsub'))
    exact hprep.trans <| hpost v ρ' st' se hΨ hse_wf heval_se

theorem compileAssert_correct (reg : Verifier.Registry) (e : Expr)
    (ih : correctExpr reg e) :
    correctExpr reg (.assert e) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  have heval_e : (compile reg Θ Δ_spec S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_assert <| ih Θ R S B Γ st ρ γ Δ_spec ρ_spec _ _
    (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se
  obtain ⟨_, _, hΨ_e⟩ := hΨ_e
  let φ := Formula.eq .bool (Term.unop .toBool se) (Term.const (.b true))
  have hwf_φ : φ.wfIn st₁.decls := by
    simpa [φ, Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn] using hse_wf
  have heval_assert : (VerifM.assert φ).eval st₁ ρ_e _ := VerifM.eval_bind _ _ _ _ hΨ_e
  obtain ⟨hφ, hcont⟩ := VerifM.eval_assert heval_assert hwf_φ
  have hΨ_pure := VerifM.eval_ret hcont
  have hvtrue : v_e = .bool true := by
    simp only [φ, Formula.eval, Term.eval, UnOp.eval, Const.denote] at hφ
    rw [heval_se] at hφ
    cases v_e <;> simp_all
  simp only [Expr.ty] at hpost
  subst hvtrue
  have hprep :
      st₁.sl Θ ρ_e ∗ TinyML.ValHasType Θ (.bool true) e.ty ∗ R ⊢
        st₁.sl Θ ρ_e ∗ TinyML.ValHasType Θ .unit .unit ∗ R :=
    sep_mono_r (sep_mono_l (true_intro.trans (TinyML.ValHasType.unit_intro Θ)))
  exact SpatialContext.wp_assert <| hprep.trans <| hpost .unit ρ_e st₁ (Term.const .unit) hΨ_pure
    trivial
    (by simp [Term.eval])

theorem compileFix_correct (reg : Verifier.Registry) (self : Binder) (args : List Binder) (retTy : TinyML.Typ) (body : Expr) :
    correctExpr reg (.fix self args retTy body) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval _hagree _hbwf _hSwf _hΔwf _hΔvars _hΔspec _hρspec _hpost
  simp only [compile] at heval
  exact (VerifM.eval_fatal heval).elim

theorem compilePrim_correct (reg : Verifier.Registry) (n : String) (ty : TinyML.Typ) :
    correctExpr reg (.prim n ty) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval _hagree _hbwf _hSwf _hΔwf _hΔvars _hΔspec _hρspec _hpost
  simp only [compile] at heval
  exact (VerifM.eval_fatal heval).elim

theorem compileRefShared_correct (reg : Verifier.Registry) (e : Expr)
    (ih : correctExpr reg e) :
    correctExpr reg (.ref false e) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  simp only [Expr.ty, Bool.false_eq_true, if_false] at hpost
  have heval_e : (compile reg Θ Δ_spec S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_ref <| ih Θ R S B Γ st ρ γ Δ_spec ρ_spec _ _
    (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se
  obtain ⟨_hdecls_e, _hagreeOn_e, hΨ_e⟩ := hΨ_e
  have hwf_st₁ := VerifM.eval.wf hΨ_e
  set c : FOL.Const := st₁.freshConst none .value
  have hfresh : c.name ∉ st₁.decls.allNames :=
    TransState.freshConst_fresh st₁ none .value
  have hwf_addConst : TransState.wf { st₁ with decls := st₁.decls.addConst c } :=
    TransState.freshConst.wf _ hwf_st₁
  have hwp :
      st₁.sl Θ ρ_e ∗ TinyML.ValHasType Θ v_e e.ty ∗ R ⊢ wp (reg.wpCtx) (.ref (.val v_e)) Φ := by
    istart
    iintro ⟨Howns, □Hty, HR⟩
    iapply (wp.ref_inv (I := fun w => TinyML.ValHasType Θ w e.ty))
    isplitl []
    · imodintro
      iexact Hty
    · iintro %loc Hinv
      have hdecl_eval := VerifM.eval_bind _ _ _ _ hΨ_e
      have hdecl := VerifM.eval_decl hdecl_eval (.loc loc)
      have hret := VerifM.eval_ret hdecl
      set ρ_e' : VerifM.Env := ρ_e.updateConst .value c.name (.loc loc)
      set st₂ : TransState := {
        decls := st₁.decls.addConst c
        asserts := st₁.asserts
        owns := st₁.owns
      }
      have hc_wf : (Term.const (.uninterpreted c.name .value)).wfIn st₂.decls :=
        by
          simpa [st₂] using
            (Term.const_wfIn_addConst_of_fresh (Δ := st₁.decls) (c := c)
              hwf_st₁.namesDisjoint hfresh)
      have hval_eval : Term.eval ρ_e'.env (Term.const (.uninterpreted c.name .value)) = .loc loc := by
        simp [Term.eval, Const.denote, ρ_e', VerifM.Env.updateConst, Env.updateConst]
      have hlocTy : locinv loc (fun w => TinyML.ValHasType Θ w e.ty) ⊢
          TinyML.ValHasType Θ (.loc loc) (.ref e.ty) := by
        refine Entails.trans ?_ (TinyML.ValHasType.ref Θ (.loc loc) e.ty).2
        iintro Hinv
        iexists loc
        isplitr
        · ipure_intro
          rfl
        · iexact Hinv
      have hsl_agree : st₁.sl Θ ρ_e ⊢ st₂.sl Θ ρ_e' := by
        simp only [TransState.sl_eq, st₂]
        apply (SpatialContext.interp_env_agree Θ hwf_st₁.ownsWf ?_).1
        exact Env.agreeOn_update_fresh_const (c := c) hfresh
      iapply (hpost (.loc loc) ρ_e' st₂ (Term.const (.uninterpreted c.name .value))
        hret hc_wf hval_eval)
      isplitl [Howns]
      · iapply hsl_agree
        iexact Howns
      · isplitl [Hinv]
        · iapply hlocTy
          iexact Hinv
        · iexact HR
  exact hwp

theorem compileRefOwned_correct (reg : Verifier.Registry) (e : Expr)
    (ih : correctExpr reg e) :
    correctExpr reg (.ref true e) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  simp only [Expr.ty, if_true] at hpost
  have heval_e : (compile reg Θ Δ_spec S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_ref <| ih Θ R S B Γ st ρ γ Δ_spec ρ_spec _ _
    (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se
  obtain ⟨_hdecls_e, _hagreeOn_e, hΨ_e⟩ := hΨ_e
  have hdecl_eval := VerifM.eval_bind _ _ _ _ hΨ_e
  set c : FOL.Const := st₁.freshConst none .value
  set sl : Term .value := .const (.uninterpreted c.name .value)
  have hdecl := VerifM.eval_decl hdecl_eval
  have hwf_st₁ := VerifM.eval.wf hΨ_e
  have hc_fresh : c.name ∉ st₁.decls.allNames :=
    TransState.freshConst_fresh st₁ none .value
  have hwp :
      st₁.sl Θ ρ_e ∗ TinyML.ValHasType Θ v_e e.ty ∗ R ⊢ wp (reg.wpCtx) (.ref (.val v_e)) Φ := by
    refine SpatialContext.wp_ref Θ
      (ctx := st₁.owns) (ρ := ρ_e.env) (R := R) (Δ := st₁.decls)
      (vt := se) (ty := e.ty) (name := c.name)
      (newctx := SpatialContext.insert (.pointsTo sl se e.ty) st₁.owns)
      hwf_st₁.ownsWf hse_wf heval_se hc_fresh rfl ?_
    intro loc
    set ρ₂ : VerifM.Env := ρ_e.updateConst .value c.name (.loc loc)
    set st₂ : TransState := { st₁ with decls := st₁.decls.addConst c }
    have hdecl_loc := hdecl (.loc loc)
    have hsl_wf : sl.wfIn st₂.decls := by
      simpa [sl, st₂] using
        (Term.const_wfIn_addConst_of_fresh (Δ := st₁.decls) (c := c)
          hwf_st₁.namesDisjoint hc_fresh)
    have hse_wf₂ : se.wfIn st₂.decls :=
      Term.wfIn_mono se hse_wf (Signature.Subset.subset_addConst _ _)
        (TransState.freshConst.wf _ hwf_st₁).namesDisjoint
    have hatom_wf : (SpatialAtom.pointsTo sl se e.ty).wfIn st₂.decls := ⟨hsl_wf, hse_wf₂⟩
    have hret := VerifM.eval_ret (VerifM.eval_assumeSpatial (VerifM.eval_bind _ _ _ _ hdecl_loc) hatom_wf)
    have hsl_eval : sl.eval ρ₂.env = .loc loc := by
      simp [sl, ρ₂, c, Term.eval, Const.denote, VerifM.Env.updateConst, Env.updateConst]
    have hlocTy : ⊢ TinyML.ValHasType Θ (.loc loc) (.owned e.ty) := by
      refine Entails.trans ?_ (TinyML.ValHasType.owned Θ (.loc loc) e.ty).2
      istart
      iintro _
      iexists loc
      ipure_intro
      rfl
    istart
    iintro ⟨Hsl, HR⟩
    iapply (hpost (.loc loc) ρ₂ { st₂ with owns := .pointsTo sl se e.ty :: st₁.owns }
      sl hret hsl_wf hsl_eval)
    isplitl [Hsl]
    · simp [TransState.sl_eq, st₂, SpatialContext.insert]
      rw [show ρ₂.env = ρ_e.env.updateConst .value c.name (.loc loc) by rfl]
      iexact Hsl
    · isplitl []
      · iapply hlocTy
      · iexact HR
  exact hwp

theorem compileRef_correct (reg : Verifier.Registry) (owned : Bool) (e : Expr)
    (ih : correctExpr reg e) :
    correctExpr reg (.ref owned e) := by
  cases owned with
  | false => exact compileRefShared_correct reg e ih
  | true => exact compileRefOwned_correct reg e ih

theorem compileDerefShared_correct (reg : Verifier.Registry) (e : Expr) (ty : TinyML.Typ)
    (href : e.ty = .ref ty)
    (ih : correctExpr reg e) :
    correctExpr reg (.deref e ty) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile, href] at heval
  simp only [Expr.ty] at hpost
  obtain ⟨_, heval⟩ := VerifM.eval_bind_expectEq heval
  have heval_e : (compile reg Θ Δ_spec S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_deref <| ih Θ R S B Γ st ρ γ Δ_spec ρ_spec _ _
    (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
  intro v_e ρ_e st₁ se hΨ_e _hse_wf heval_se
  obtain ⟨_hdecls_e, _hagreeOn_e, hΨ_e⟩ := hΨ_e
  have hdecl_eval := VerifM.eval_bind _ _ _ _ hΨ_e
  have hdecl := VerifM.eval_decl hdecl_eval
  set c : FOL.Const := st₁.freshConst none .value
  set sv : Term .value := .const (.uninterpreted c.name .value)
  have hc_fresh : c.name ∉ st₁.decls.allNames :=
    TransState.freshConst_fresh st₁ none .value
  have hc_wf : sv.wfIn (st₁.decls.addConst c) :=
    by
      simpa [sv] using
        (Term.const_wfIn_addConst_of_fresh (Δ := st₁.decls) (c := c)
          (VerifM.eval.wf hdecl_eval).namesDisjoint hc_fresh)
  have hwp :
      st₁.sl Θ ρ_e ∗ TinyML.ValHasType Θ v_e e.ty ∗ R ⊢ wp (reg.wpCtx) (.deref (.val v_e)) Φ := by
    rw [href]
    istart
    iintro ⟨Howns, Href, HR⟩
    ihave Href' := (TinyML.ValHasType.ref Θ v_e ty).1 $$ Href
    icases Href' with ⟨%loc, %hvloc, Hinv⟩
    subst hvloc
    iapply (wp.deref_inv (l := loc) (I := fun w => TinyML.ValHasType Θ w ty))
    isplitl [Hinv]
    · iexact Hinv
    · iintro %w #Hw
      have hdecl_w := hdecl w
      have hassume_eval := VerifM.eval_bind _ _ _ _ hdecl_w
      set ρ₂ : VerifM.Env := ρ_e.updateConst .value c.name w
      set st₂ : TransState := { st₁ with decls := st₁.decls.addConst c }
      have hsv_eval : sv.eval ρ₂.env = w := by
        simp [sv, ρ₂, Term.eval, Const.denote, VerifM.Env.updateConst, Env.updateConst]
      ihave Hcheck := TinyML.typeConstraints_hold (ty := ty) (t := sv)
        (ρ := ρ₂.env) (Θ := Θ) (v := w) hsv_eval $$ Hw
      ipure Hcheck
      obtain ⟨st₃, hst₃_decls, hst₃_owns, _, heval_ret⟩ := VerifM.eval_assumeAll hassume_eval
        (fun φ hφ => TinyML.typeConstraints_wfIn hc_wf φ hφ)
        (fun φ hφ => Hcheck φ hφ)
      have hΨ_ret := VerifM.eval_ret heval_ret
      have hsv_wf : sv.wfIn st₃.decls := hst₃_decls ▸ hc_wf
      have hsl_agree : st₁.sl Θ ρ_e ⊢ st₃.sl Θ ρ₂ := by
        simp [TransState.sl_eq, st₂, hst₃_owns]
        exact (SpatialContext.interp_env_agree Θ (VerifM.eval.wf hdecl_eval).ownsWf
          (Env.agreeOn_update_fresh_const (c := c) hc_fresh)).1
      iapply (hpost w ρ₂ st₃ sv hΨ_ret hsv_wf hsv_eval)
      isplitl [Howns]
      · iapply hsl_agree
        iexact Howns
      · isplitl []
        · iexact Hw
        · iexact HR
  exact hwp

theorem compileDerefOwned_correct (reg : Verifier.Registry) (e : Expr) (ty : TinyML.Typ)
    (howned : e.ty = .owned ty)
    (ih : correctExpr reg e) :
    correctExpr reg (.deref e ty) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile, howned] at heval
  simp only [Expr.ty] at hpost
  obtain ⟨_, heval⟩ := VerifM.eval_bind_expectEq heval
  have heval_e : (compile reg Θ Δ_spec S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_deref <| ih Θ R S B Γ st ρ γ Δ_spec ρ_spec _ _
    (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se
  obtain ⟨_hdecls_e, _hagreeOn_e, hΨ_e⟩ := hΨ_e
  have hfind_eval := VerifM.eval_bind _ _ _ _ hΨ_e
  rw [howned]
  refine VerifM.eval_findMatchForce Θ
    (R := TinyML.ValHasType Θ v_e (.owned ty) ∗ R)
    (Φ := wp (reg.wpCtx) (.deref (.val v_e)) Φ) hfind_eval hse_wf ?_
  intro v st₂ hQ hdecls hv_wf
  have hassume_eval := VerifM.eval_bind _ _ _ _ hQ
  have hatom_wf : (SpatialAtom.pointsTo se v ty).wfIn st₂.decls := by
    rw [hdecls]
    exact ⟨hse_wf, hv_wf⟩
  have hassume := VerifM.eval_assumeSpatial hassume_eval hatom_wf
  have hret := VerifM.eval_ret hassume
  have hv_wf' : v.wfIn st₂.decls := by
    rw [hdecls]
    exact hv_wf
  have hwp :
      SpatialAtom.interp Θ ρ_e.env (.pointsTo se v ty) ∗ st₂.sl Θ ρ_e ∗
        (TinyML.ValHasType Θ v_e (.owned ty) ∗ R) ⊢ wp (reg.wpCtx) (.deref (.val v_e)) Φ := by
    simp only [SpatialAtom.interp]
    istart
    iintro ⟨Hatom, Howns, _Howned, HR⟩
    icases Hatom with ⟨%loc, %hse_loc, Hpt, #HstoredTy⟩
    have hse_loc_orig : se.eval ρ_e.env = .loc loc := hse_loc
    rw [heval_se] at hse_loc
    rw [hse_loc]
    iapply (wp.deref (l := loc) (v := v.eval ρ_e.env))
    isplitl [Hpt]
    · iexact Hpt
    · iintro Hpt
      iapply (hpost (v.eval ρ_e.env) ρ_e { st₂ with owns := .pointsTo se v ty :: st₂.owns }
        v hret hv_wf' rfl)
      isplitl [Hpt HstoredTy Howns]
      · simp [TransState.sl_eq]
        isplitl [Hpt HstoredTy]
        · simp [SpatialAtom.interp]
          iexists loc
          isplitr
          · ipure_intro
            exact hse_loc_orig
          · isplitl [Hpt]
            · iexact Hpt
            · iexact HstoredTy
        · iexact Howns
      · isplitl [HstoredTy]
        · iexact HstoredTy
        · iexact HR
  exact hwp

theorem compileDeref_correct (reg : Verifier.Registry) (e : Expr) (ty : TinyML.Typ)
    (ih : correctExpr reg e) :
    correctExpr reg (.deref e ty) := by
  cases hty : e.ty with
  | ref ty' =>
      by_cases heq : ty' = ty
      · have href : e.ty = .ref ty := by simpa [heq] using hty
        exact compileDerefShared_correct reg e ty href ih
      · intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval _ _ _ _ _ _ _ _
        simp only [compile, hty] at heval
        obtain ⟨hannot, _⟩ := VerifM.eval_bind_expectEq heval
        exact False.elim (heq hannot)
  | owned ty' =>
      by_cases heq : ty' = ty
      · have howned : e.ty = .owned ty := by simpa [heq] using hty
        exact compileDerefOwned_correct reg e ty howned ih
      · intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval _ _ _ _ _ _ _ _
        simp only [compile, hty] at heval
        obtain ⟨hannot, _⟩ := VerifM.eval_bind_expectEq heval
        exact False.elim (heq hannot)
  | prim _ | sum _ | arrow _ _ | empty | value | tuple _ | tvar _ | named _ _ =>
      intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval _ _ _ _ _ _ _ _
      simp only [compile, hty] at heval
      exact (VerifM.eval_fatal heval).elim

theorem compileStoreShared_correct (reg : Verifier.Registry) (loc val : Expr)
    (href : loc.ty = .ref val.ty)
    (ihVal : correctExpr reg val) (ihLoc : correctExpr reg loc) :
    correctExpr reg (.store loc val) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile, href] at heval
  simp only [Expr.ty] at hpost
  obtain ⟨_, heval⟩ := VerifM.eval_bind_expectEq heval
  have heval_v : (compile reg Θ Δ_spec S B Γ val).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  have hstart :
      st.sl Θ ρ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) ⊢
        st.sl Θ ρ ∗
          (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗
            (Bindings.typedSubst Θ B Γ γ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R))) :=
    Helpers.ctx_dup_flip reg Θ Δ_spec ρ_spec S B Γ st ρ γ R
  refine SpatialContext.wp_bind_store <| (hstart.trans <|
    ihVal Θ (Bindings.typedSubst Θ B Γ γ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R)) S B Γ st ρ γ Δ_spec ρ_spec _ _
      (VerifM.eval.decls_grow ρ heval_v) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_)
  intro v_v ρ_v st₁ sv hΨ_v hsv_wf heval_sv
  obtain ⟨hdecls_v, hagreeOn_v, hΨ_v⟩ := hΨ_v
  have hagree_v : B.agreeOnLinked ρ_v.env γ :=
    Bindings.agreeOnLinked_env_agree hagree hagreeOn_v hbwf
  have hbwf_v : B.wfIn st₁.decls := fun p hp => hdecls_v.consts _ (hbwf p hp)
  have heval_l : (compile reg Θ Δ_spec S B Γ loc).eval st₁ ρ_v _ := VerifM.eval_bind _ _ _ _ hΨ_v
  have hlocStart :
      st₁.sl Θ ρ_v ∗ TinyML.ValHasType Θ v_v val.ty ∗
        (Bindings.typedSubst Θ B Γ γ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R)) ⊢
          st₁.sl Θ ρ_v ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗
            (TinyML.ValHasType Θ v_v val.ty ∗ R)) :=
    Helpers.ctx_push_flip reg Θ Δ_spec ρ_spec S B Γ st₁ ρ_v γ R v_v val.ty
  have hspecInv_v := specInvariants_mono hΔspec hρspec hdecls_v hagreeOn_v
  refine hlocStart.trans <| ihLoc Θ (TinyML.ValHasType Θ v_v val.ty ∗ R) S B Γ st₁ ρ_v γ Δ_spec ρ_spec _ _
    (VerifM.eval.decls_grow ρ_v heval_l) hagree_v hbwf_v hSwf hΔwf hΔvars hspecInv_v.1 hspecInv_v.2 hΔreg hρreg ?_
  intro v_l ρ_l st₂ sl hΨ_l hsl_wf heval_sl
  obtain ⟨hdecls_l, hagreeOn_l, hΨ_l⟩ := hΨ_l
  obtain hret := VerifM.eval_ret hΨ_l
  have hunit_wf : (Term.const .unit).wfIn st₂.decls := by
    simp [Term.wfIn, Const.wfIn]
  have hgoal :
      st₂.sl Θ ρ_l ∗ TinyML.ValHasType Θ .unit .unit ∗ R ⊢ Φ .unit :=
    hpost .unit ρ_l st₂ _ hret hunit_wf (by simp [Term.eval])
  have hwp :
      st₂.sl Θ ρ_l ∗ (TinyML.ValHasType Θ v_l loc.ty ∗ (TinyML.ValHasType Θ v_v val.ty ∗ R)) ⊢
        wp (reg.wpCtx) (.store (.val v_l) (.val v_v)) Φ := by
    rw [href]
    istart
    iintro ⟨Howns, Hloc, #Hval, HR⟩
    ihave Href := (TinyML.ValHasType.ref Θ v_l val.ty).1 $$ Hloc
    icases Href with ⟨%lref, %hv_l, Hinv⟩
    subst hv_l
    iapply (wp.store_inv (l := lref) (v := v_v) (I := fun w => TinyML.ValHasType Θ w val.ty))
    isplitl [Hinv]
    · iexact Hinv
    · isplitl []
      · imodintro
        iexact Hval
      · iapply hgoal
        isplitl [Howns]
        · iexact Howns
        · isplitl []
          · iapply (TinyML.ValHasType.unit_intro Θ)
          · iexact HR
  exact hwp

theorem compileStoreOwned_correct (reg : Verifier.Registry) (loc val : Expr)
    (howned : loc.ty = .owned val.ty)
    (ihVal : correctExpr reg val) (ihLoc : correctExpr reg loc) :
    correctExpr reg (.store loc val) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile, howned] at heval
  simp only [Expr.ty] at hpost
  obtain ⟨_, heval⟩ := VerifM.eval_bind_expectEq heval
  have heval_v : (compile reg Θ Δ_spec S B Γ val).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  have hstart :
      st.sl Θ ρ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) ⊢
        st.sl Θ ρ ∗
          (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗
            (Bindings.typedSubst Θ B Γ γ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R))) :=
    Helpers.ctx_dup_flip reg Θ Δ_spec ρ_spec S B Γ st ρ γ R
  refine SpatialContext.wp_bind_store <| (hstart.trans <|
    ihVal Θ (Bindings.typedSubst Θ B Γ γ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R)) S B Γ st ρ γ Δ_spec ρ_spec _ _
      (VerifM.eval.decls_grow ρ heval_v) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_)
  intro v_v ρ_v st₁ sv hΨ_v hsv_wf heval_sv
  obtain ⟨hdecls_v, hagreeOn_v, hΨ_v⟩ := hΨ_v
  have hagree_v : B.agreeOnLinked ρ_v.env γ :=
    Bindings.agreeOnLinked_env_agree hagree hagreeOn_v hbwf
  have hbwf_v : B.wfIn st₁.decls := fun p hp => hdecls_v.consts _ (hbwf p hp)
  have heval_l : (compile reg Θ Δ_spec S B Γ loc).eval st₁ ρ_v _ := VerifM.eval_bind _ _ _ _ hΨ_v
  have hlocStart :
      st₁.sl Θ ρ_v ∗ TinyML.ValHasType Θ v_v val.ty ∗
        (Bindings.typedSubst Θ B Γ γ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R)) ⊢
          st₁.sl Θ ρ_v ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗
            (TinyML.ValHasType Θ v_v val.ty ∗ R)) :=
    Helpers.ctx_push_flip reg Θ Δ_spec ρ_spec S B Γ st₁ ρ_v γ R v_v val.ty
  have hspecInv_v := specInvariants_mono hΔspec hρspec hdecls_v hagreeOn_v
  refine hlocStart.trans <| ihLoc Θ (TinyML.ValHasType Θ v_v val.ty ∗ R) S B Γ st₁ ρ_v γ Δ_spec ρ_spec _ _
    (VerifM.eval.decls_grow ρ_v heval_l) hagree_v hbwf_v hSwf hΔwf hΔvars hspecInv_v.1 hspecInv_v.2 hΔreg hρreg ?_
  intro v_l ρ_l st₂ sl hΨ_l hsl_wf heval_sl
  obtain ⟨_hdecls_l, _hagreeOn_l, hΨ_l⟩ := hΨ_l
  have hfind_eval := VerifM.eval_bind _ _ _ _ hΨ_l
  have hsv_wf_l : sv.wfIn st₂.decls :=
    Term.wfIn_mono sv hsv_wf _hdecls_l (VerifM.eval.wf hΨ_l).namesDisjoint
  have heval_sv_l : sv.eval ρ_l.env = v_v := by
    rw [← Term.eval_env_agree hsv_wf _hagreeOn_l]
    exact heval_sv
  rw [howned]
  refine VerifM.eval_findMatchForce Θ
    (R := TinyML.ValHasType Θ v_l (.owned val.ty) ∗ (TinyML.ValHasType Θ v_v val.ty ∗ R))
    (Φ := wp (reg.wpCtx) (.store (.val v_l) (.val v_v)) Φ) hfind_eval hsl_wf ?_
  intro old st₃ hQ hdecls hold_wf
  have hassume_eval := VerifM.eval_bind _ _ _ _ hQ
  have hatom_wf : (SpatialAtom.pointsTo sl sv val.ty).wfIn st₃.decls := by
    rw [hdecls]
    exact ⟨hsl_wf, hsv_wf_l⟩
  have hassume := VerifM.eval_assumeSpatial hassume_eval hatom_wf
  have hret := VerifM.eval_ret hassume
  have hunit_wf : (Term.const .unit).wfIn ({ st₃ with owns := .pointsTo sl sv val.ty :: st₃.owns }).decls := by
    simp [Term.wfIn, Const.wfIn]
  have hwp :
      SpatialAtom.interp Θ ρ_l.env (.pointsTo sl old val.ty) ∗ st₃.sl Θ ρ_l ∗
        (TinyML.ValHasType Θ v_l (.owned val.ty) ∗ (TinyML.ValHasType Θ v_v val.ty ∗ R)) ⊢
          wp (reg.wpCtx) (.store (.val v_l) (.val v_v)) Φ := by
    simp only [SpatialAtom.interp]
    istart
    iintro ⟨Hatom, Howns, _Howned, #HnewTy, HR⟩
    icases Hatom with ⟨%lref, %hsl_loc, Hold, _HoldTy⟩
    have hsl_loc_orig : sl.eval ρ_l.env = .loc lref := hsl_loc
    rw [heval_sl] at hsl_loc
    rw [hsl_loc]
    iapply (wp.store (l := lref) (old := old.eval ρ_l.env) (v := v_v))
    isplitl [Hold]
    · iexact Hold
    · iintro Hnew
      iapply (hpost .unit ρ_l { st₃ with owns := .pointsTo sl sv val.ty :: st₃.owns }
        (Term.const .unit) hret hunit_wf (by simp [Term.eval]))
      isplitl [Hnew HnewTy Howns]
      · simp [TransState.sl_eq]
        isplitl [Hnew HnewTy]
        · simp [SpatialAtom.interp]
          iexists lref
          isplitr
          · ipure_intro
            exact hsl_loc_orig
          · isplitl [Hnew]
            · rw [heval_sv_l]
              iexact Hnew
            · rw [heval_sv_l]
              iexact HnewTy
        · iexact Howns
      · isplitl []
        · iapply (TinyML.ValHasType.unit_intro Θ)
        · iexact HR
  exact hwp

theorem compileStore_correct (reg : Verifier.Registry) (loc val : Expr)
    (ihVal : correctExpr reg val) (ihLoc : correctExpr reg loc) :
    correctExpr reg (.store loc val) := by
  cases hty : loc.ty with
  | ref ty =>
      by_cases heq : ty = val.ty
      · have href : loc.ty = .ref val.ty := by simpa [heq] using hty
        exact compileStoreShared_correct reg loc val href ihVal ihLoc
      · intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval _ _ _ _ _ _ _ _
        simp only [compile, hty] at heval
        obtain ⟨hannot, _⟩ := VerifM.eval_bind_expectEq heval
        exact False.elim (heq hannot)
  | owned ty =>
      by_cases heq : ty = val.ty
      · have howned : loc.ty = .owned val.ty := by simpa [heq] using hty
        exact compileStoreOwned_correct reg loc val howned ihVal ihLoc
      · intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval _ _ _ _ _ _ _ _
        simp only [compile, hty] at heval
        obtain ⟨hannot, _⟩ := VerifM.eval_bind_expectEq heval
        exact False.elim (heq hannot)
  | prim _ | sum _ | arrow _ _ | empty | value | tuple _ | tvar _ | named _ _ =>
      intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval _ _ _ _ _ _ _ _
      simp only [compile, hty] at heval
      exact (VerifM.eval_fatal heval).elim

theorem compileUnop_correct (reg : Verifier.Registry) (op : TinyML.UnOp) (e : Expr) (uty : TinyML.Typ)
    (ih : correctExpr reg e) :
    correctExpr reg (.unop op e uty) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  have heval_e : (compile reg Θ Δ_spec S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_unop <| ih Θ R S B Γ st ρ γ Δ_spec ρ_spec _ _
    (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se
  obtain ⟨_, _, hΨ_e⟩ := hΨ_e
  obtain ⟨ty, htypeOf, hΨ_e⟩ := VerifM.eval_bind_expectSome hΨ_e
  obtain ⟨hty_eq, hΨ_e⟩ := VerifM.eval_bind_expectEq hΨ_e
  obtain ⟨t, hcompUnop, hΨ_e⟩ := VerifM.eval_bind_expectSome hΨ_e
  obtain hΨ_e := VerifM.eval_ret hΨ_e
  have htyped :
      st₁.sl Θ ρ_e ∗ TinyML.ValHasType Θ v_e e.ty ∗ R ⊢
        st₁.sl Θ ρ_e ∗ iprop(∃ w, ⌜TinyML.evalUnOp op v_e = some w⌝ ∗ TinyML.ValHasType Θ w ty) ∗ R :=
    sep_mono_r (sep_mono_l (TinyML.evalUnOp_typed htypeOf))
  simp only [Expr.ty] at hpost
  refine htyped.trans ?_
  istart
  iintro ⟨Howns, Hex, HR⟩
  icases Hex with ⟨%w, %heval_op, Hwty⟩
  have ht_eval : t.eval ρ_e.env = w :=
    compileUnop_eval heval_se heval_op hcompUnop
  have hq : st₁.sl Θ ρ_e ∗ TinyML.ValHasType Θ w ty ∗ R ⊢ Φ w :=
    by simpa [hty_eq] using
      (hpost w ρ_e st₁ t hΨ_e (compileUnop_wfIn hse_wf hcompUnop) ht_eval)
  have hwp : st₁.sl Θ ρ_e ∗ TinyML.ValHasType Θ w ty ∗ R ⊢ wp (reg.wpCtx) (.unop op (.val v_e)) Φ :=
    SpatialContext.wp_unop
      (R := st₁.sl Θ ρ_e ∗ TinyML.ValHasType Θ w ty ∗ R)
      (Q := Φ) (op := op) (v := v_e) (res := w) hq heval_op
  iapply hwp
  isplitl [Howns]
  · iexact Howns
  · isplitl [Hwty]
    · iexact Hwty
    · iexact HR

theorem compileBinop_correct (reg : Verifier.Registry) (op : TinyML.BinOp) (l r : Expr) (bty : TinyML.Typ)
    (ihR : correctExpr reg r) (ihL : correctExpr reg l) :
    correctExpr reg (.binop op l r bty) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  have heval_r : (compile reg Θ Δ_spec S B Γ r).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  have hstart :
      st.sl Θ ρ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) ⊢
        st.sl Θ ρ ∗
          (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗
            (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R)) :=
    Helpers.ctx_dup reg Θ Δ_spec ρ_spec S B Γ st ρ γ R
  refine SpatialContext.wp_bind_binop <| hstart.trans <|
    ihR Θ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) S B Γ st ρ γ Δ_spec ρ_spec _ _
      (VerifM.eval.decls_grow ρ heval_r) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
  intro vr ρ_r st₁ sr hΨ_r hsr_wf heval_sr
  obtain ⟨hdecls_r, hagreeOn_r, hΨ_r⟩ := hΨ_r
  have hagree_r : B.agreeOnLinked ρ_r.env γ :=
    Bindings.agreeOnLinked_env_agree hagree hagreeOn_r hbwf
  have hbwf_r : B.wfIn st₁.decls := fun p hp => hdecls_r.consts _ (hbwf p hp)
  have heval_l : (compile reg Θ Δ_spec S B Γ l).eval st₁ ρ_r _ := VerifM.eval_bind _ _ _ _ hΨ_r
  have hleftStart :
      st₁.sl Θ ρ_r ∗ TinyML.ValHasType Θ vr r.ty ∗
        (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) ⊢
          st₁.sl Θ ρ_r ∗
            (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗
              (TinyML.ValHasType Θ vr r.ty ∗ R)) :=
    Helpers.ctx_push reg Θ Δ_spec ρ_spec S B Γ st₁ ρ_r γ R vr r.ty
  have hspecInv_r := specInvariants_mono hΔspec hρspec hdecls_r hagreeOn_r
  refine hleftStart.trans <|
    ihL Θ (TinyML.ValHasType Θ vr r.ty ∗ R) S B Γ st₁ ρ_r γ Δ_spec ρ_spec _ _
      (VerifM.eval.decls_grow ρ_r heval_l) hagree_r hbwf_r hSwf hΔwf hΔvars hspecInv_r.1 hspecInv_r.2 hΔreg hρreg ?_
  intro vl ρ_l st₂ sl hΨ_l hsl_wf heval_sl
  obtain ⟨hdecls_l, hagreeOn_l, hΨ_l⟩ := hΨ_l
  obtain ⟨ty, htypeOf, hΨ_l⟩ := VerifM.eval_bind_expectSome hΨ_l
  obtain ⟨hty_eq, hΨ_l'⟩ := VerifM.eval_bind_expectEq hΨ_l
  simp only [Expr.ty] at hpost
  have hsr_ρ_l : sr.eval ρ_l.env = vr := by
    rw [Term.eval_env_agree hsr_wf (Env.agreeOn_symm hagreeOn_l)]
    exact heval_sr
  by_cases hdivmod : op = .div ∨ op = .mod
  · have hΨ_div :
          (do
            let i t := Term.unop UnOp.toInt t
            let fol_op := if op == TinyML.BinOp.div then BinOp.div else BinOp.mod
            VerifM.assert (.not (.eq .int (i sr) (.const (.i 0))))
            pure (Term.unop .ofInt (Term.binop fol_op (i sl) (i sr)))).eval st₂ ρ_l Ψ := by
      simpa [hdivmod] using hΨ_l'
    rcases hdivmod with hdiv | hmod
    · subst hdiv
      obtain ⟨hlty, hrty, hty_int⟩ :=
        TinyML.BinOp.typeOf_arith (op := .div) (by simp) htypeOf
      have hassert_wf : (Formula.not (.eq .int (.unop .toInt sr) (.const (.i 0)))).wfIn st₂.decls := by
        simpa [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn] using
          (Term.wfIn_mono sr hsr_wf hdecls_l (VerifM.eval.wf hΨ_div).namesDisjoint)
      have heval_assert := VerifM.eval_bind _ _ _ _ hΨ_div
      have ⟨hne_zero, hΨ_post⟩ := VerifM.eval_assert heval_assert hassert_wf
      simp [Formula.eval, Term.eval, Const.denote] at hne_zero
      rw [hsr_ρ_l] at hne_zero
      obtain hΨ_post := VerifM.eval_ret hΨ_post
      have hbty : bty = .int := hty_eq.symm.trans hty_int
      have hwf_sr_l : sr.wfIn st₂.decls :=
        Term.wfIn_mono sr hsr_wf hdecls_l (VerifM.eval.wf hΨ_div).namesDisjoint
      have hwf_bin : (Term.unop .ofInt (Term.binop BinOp.div (Term.unop .toInt sl) (Term.unop .toInt sr))).wfIn st₂.decls := by
        simpa [Term.wfIn, BinOp.wfIn, UnOp.wfIn] using And.intro hsl_wf hwf_sr_l
      have hΨ_post' : Ψ (Term.unop .ofInt (Term.binop BinOp.div (Term.unop .toInt sl) (Term.unop .toInt sr))) st₂ ρ_l := by
        simpa using hΨ_post
      have hwp_int :
          st₂.sl Θ ρ_l ∗
              (TinyML.ValHasType Θ vl .int ∗ (TinyML.ValHasType Θ vr .int ∗ R)) ⊢
            wp (reg.wpCtx) (.binop .div (.val vl) (.val vr)) Φ := by
        istart
        iintro H
        icases H with ⟨Howns, Hvl, Hvr, HR⟩
        ihave Hvl_int := (TinyML.ValHasType.int Θ vl).1 $$ Hvl
        ihave Hvr_int := (TinyML.ValHasType.int Θ vr).1 $$ Hvr
        icases Hvl_int with ⟨%a, %hvl⟩
        icases Hvr_int with ⟨%b, %hvr⟩
        subst hvl hvr
        have hq : st₂.sl Θ ρ_l ∗ R ⊢ Φ (.int (a / b)) := by
          have htype : ⊢ TinyML.ValHasType Θ (.int (a / b)) .int := by
            exact TinyML.ValHasType.int_intro Θ (a / b)
          have hgoal :
              st₂.sl Θ ρ_l ∗ TinyML.ValHasType Θ (.int (a / b)) .int ∗ R ⊢ Φ (.int (a / b)) := by
            simpa [hbty] using
              (hpost (.int (a / b)) ρ_l st₂ _ hΨ_post' hwf_bin
                (by simp [Term.eval, UnOp.eval, BinOp.eval, heval_sl, hsr_ρ_l]))
          iintro ⟨Howns, HR⟩
          iapply hgoal
          isplitl [Howns]
          · iexact Howns
          · isplitl []
            · exact htype
            · iexact HR
        iapply (SpatialContext.wp_binop (vl := .int a) (vr := .int b) (res := .int (a / b)) hq)
        · simp [TinyML.evalBinOp, hne_zero]
        · isplitl [Howns]
          · iexact Howns
          · iexact HR
      simpa [hlty, hrty] using hwp_int
    · subst hmod
      obtain ⟨hlty, hrty, hty_int⟩ :=
        TinyML.BinOp.typeOf_arith (op := .mod) (by simp) htypeOf
      have hassert_wf : (Formula.not (.eq .int (.unop .toInt sr) (.const (.i 0)))).wfIn st₂.decls := by
        simpa [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn] using
          (Term.wfIn_mono sr hsr_wf hdecls_l (VerifM.eval.wf hΨ_div).namesDisjoint)
      have heval_assert := VerifM.eval_bind _ _ _ _ hΨ_div
      have ⟨hne_zero, hΨ_post⟩ := VerifM.eval_assert heval_assert hassert_wf
      simp [Formula.eval, Term.eval, Const.denote] at hne_zero
      rw [hsr_ρ_l] at hne_zero
      obtain hΨ_post := VerifM.eval_ret hΨ_post
      have hbty : bty = .int := hty_eq.symm.trans hty_int
      have hwf_sr_l : sr.wfIn st₂.decls :=
        Term.wfIn_mono sr hsr_wf hdecls_l (VerifM.eval.wf hΨ_div).namesDisjoint
      have hwf_bin : (Term.unop .ofInt (Term.binop BinOp.mod (Term.unop .toInt sl) (Term.unop .toInt sr))).wfIn st₂.decls := by
        simpa [Term.wfIn, BinOp.wfIn, UnOp.wfIn] using And.intro hsl_wf hwf_sr_l
      have hΨ_post' : Ψ (Term.unop .ofInt (Term.binop BinOp.mod (Term.unop .toInt sl) (Term.unop .toInt sr))) st₂ ρ_l := by
        simpa using hΨ_post
      have hwp_int :
          st₂.sl Θ ρ_l ∗
              (TinyML.ValHasType Θ vl .int ∗ (TinyML.ValHasType Θ vr .int ∗ R)) ⊢
            wp (reg.wpCtx) (.binop .mod (.val vl) (.val vr)) Φ := by
        istart
        iintro H
        icases H with ⟨Howns, Hvl, Hvr, HR⟩
        ihave Hvl_int := (TinyML.ValHasType.int Θ vl).1 $$ Hvl
        ihave Hvr_int := (TinyML.ValHasType.int Θ vr).1 $$ Hvr
        icases Hvl_int with ⟨%a, %hvl⟩
        icases Hvr_int with ⟨%b, %hvr⟩
        subst hvl hvr
        have hq : st₂.sl Θ ρ_l ∗ R ⊢ Φ (.int (a % b)) := by
          have htype : ⊢ TinyML.ValHasType Θ (.int (a % b)) .int := by
            exact TinyML.ValHasType.int_intro Θ (a % b)
          have hgoal :
              st₂.sl Θ ρ_l ∗ TinyML.ValHasType Θ (.int (a % b)) .int ∗ R ⊢ Φ (.int (a % b)) := by
            simpa [hbty] using
              (hpost (.int (a % b)) ρ_l st₂ _ hΨ_post' hwf_bin
                (by simp [Term.eval, UnOp.eval, BinOp.eval, heval_sl, hsr_ρ_l]))
          iintro ⟨Howns, HR⟩
          iapply hgoal
          isplitl [Howns]
          · iexact Howns
          · isplitl []
            · exact htype
            · iexact HR
        iapply (SpatialContext.wp_binop (vl := .int a) (vr := .int b) (res := .int (a % b)) hq)
        · simp [TinyML.evalBinOp, hne_zero]
        · isplitl [Howns]
          · iexact Howns
          · iexact HR
      simpa [hlty, hrty] using hwp_int
  · have hndivmod : ¬(op = TinyML.BinOp.div ∨ op = TinyML.BinOp.mod) := hdivmod
    have hΨ_ndiv :
          (do
            let t ← VerifM.expectSome
              s!"unsupported binary operator: {repr op}"
              (compileOp op sl sr)
            pure t).eval st₂ ρ_l Ψ := by
      simpa [hndivmod] using hΨ_l'
    obtain ⟨t, hcompOp, hΨ_ndiv⟩ := VerifM.eval_bind_expectSome hΨ_ndiv
    have hprep :
        st₂.sl Θ ρ_l ∗ (TinyML.ValHasType Θ vl l.ty ∗ (TinyML.ValHasType Θ vr r.ty ∗ R)) ⊢
          st₂.sl Θ ρ_l ∗ ((TinyML.ValHasType Θ vl l.ty ∗ TinyML.ValHasType Θ vr r.ty) ∗ R) := by
      iintro ⟨Howns, Hvl, Hvr, HR⟩
      isplitl [Howns]
      · iexact Howns
      · isplitl [Hvl Hvr]
        · isplitl [Hvl]
          · iexact Hvl
          · iexact Hvr
        · iexact HR
    have htyped :
        st₂.sl Θ ρ_l ∗ (TinyML.ValHasType Θ vl l.ty ∗ (TinyML.ValHasType Θ vr r.ty ∗ R)) ⊢
          st₂.sl Θ ρ_l ∗ iprop(∃ w, ⌜TinyML.evalBinOp op vl vr = some w⌝ ∗ TinyML.ValHasType Θ w ty) ∗ R :=
      hprep.trans <|
        (sep_mono_r (sep_mono_l (TinyML.evalBinOp_typed
          (fun h => hndivmod (Or.inl h))
          (fun h => hndivmod (Or.inr h))
          htypeOf)) :
          st₂.sl Θ ρ_l ∗ ((TinyML.ValHasType Θ vl l.ty ∗ TinyML.ValHasType Θ vr r.ty) ∗ R) ⊢
            st₂.sl Θ ρ_l ∗ iprop(∃ w, ⌜TinyML.evalBinOp op vl vr = some w⌝ ∗ TinyML.ValHasType Θ w ty) ∗ R)
    have hwfst₂ : st₂.decls.wf := (VerifM.eval.wf hΨ_ndiv).namesDisjoint
    obtain hΨ_ndiv := VerifM.eval_ret hΨ_ndiv
    have hwf_sr_l : sr.wfIn st₂.decls :=
      Term.wfIn_mono sr hsr_wf hdecls_l hwfst₂
    refine htyped.trans ?_
    istart
    iintro ⟨Howns, Hex, HR⟩
    icases Hex with ⟨%w, %heval_op, Hwty⟩
    have ht_eval : t.eval ρ_l.env = w := compileOp_eval heval_sl hsr_ρ_l heval_op hcompOp
    have hq : st₂.sl Θ ρ_l ∗ TinyML.ValHasType Θ w ty ∗ R ⊢ Φ w := by
      simpa [hty_eq] using
        (hpost w ρ_l st₂ t hΨ_ndiv (compileOp_wfIn hsl_wf hwf_sr_l hcompOp) ht_eval)
    have hwp : st₂.sl Θ ρ_l ∗ TinyML.ValHasType Θ w ty ∗ R ⊢ wp (reg.wpCtx) (.binop op (.val vl) (.val vr)) Φ :=
      SpatialContext.wp_binop
        (R := st₂.sl Θ ρ_l ∗ TinyML.ValHasType Θ w ty ∗ R)
        (Q := Φ) (op := op) (vl := vl) (vr := vr) (res := w) hq heval_op
    iapply hwp
    isplitl [Howns]
    · iexact Howns
    · isplitl [Hwty]
      · iexact Hwty
      · iexact HR

theorem compileLetIn_correct (reg : Verifier.Registry) (b : Binder) (e body : Expr)
    (ihE : correctExpr reg e) (ihBody : correctExpr reg body) :
    correctExpr reg (.letIn b e body) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  simp only [compile] at heval
  simp only [Expr.ty] at hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.letIn_subst]
  have heval_e_outer : (compile reg Θ Δ_spec S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  have hstart :
      st.sl Θ ρ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) ⊢
        st.sl Θ ρ ∗
          (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗
            (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R)) :=
    Helpers.ctx_dup reg Θ Δ_spec ρ_spec S B Γ st ρ γ R
  refine (hstart.trans <| ihE Θ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) S B Γ st ρ γ Δ_spec ρ_spec _ _
    (VerifM.eval.decls_grow ρ heval_e_outer) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_).trans wp.letIn
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_e
  obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
  have hagree_e := Bindings.agreeOnLinked_env_agree hagree hagreeOn_e hbwf
  have hbwf_e : B.wfIn st₁.decls := fun p hp => hdecls_e.consts _ (hbwf p hp)
  obtain ⟨_, hΨ_e⟩ := VerifM.eval_bind_expectEq hΨ_e
  cases hname : b.name with
  | none =>
    simp [hname] at hΨ_e
    have hdrop :
        st₁.sl Θ ρ_e ∗ (TinyML.ValHasType Θ v_e e.ty ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R)) ⊢
          st₁.sl Θ ρ_e ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) := by
      iintro ⟨Howns, _Hv, □HS, □HT, HR⟩
      isplitl [Howns]
      · iexact Howns
      · isplitl []
        · iexact HS
        · isplitl []
          · iexact HT
          · iexact HR
    have hspecInv_e := specInvariants_mono hΔspec hρspec hdecls_e hagreeOn_e
    have hbody := hdrop.trans <| ihBody Θ R S B Γ st₁ ρ_e γ Δ_spec ρ_spec _ _
      (VerifM.eval.decls_grow ρ_e hΨ_e) hagree_e hbwf_e hSwf hΔwf hΔvars hspecInv_e.1 hspecInv_e.2 hΔreg hρreg
      (fun v ρ' st' se hΨ hs hw =>
        let ⟨_, _, hΨ'⟩ := hΨ
        hpost v ρ' st' se hΨ' hs hw)
    have hsubst := Runtime.Expr.subst_remove'_updateBinder body.runtime γ Runtime.Binder.none v_e
    have hbody' : st₁.sl Θ ρ_e ∗
          (TinyML.ValHasType Θ v_e e.ty ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R)) ⊢
            wp (reg.wpCtx)
              (Runtime.Expr.subst
                (Runtime.Subst.updateBinder Runtime.Binder.none v_e Runtime.Subst.id)
                (Runtime.Expr.subst (γ.remove' Runtime.Binder.none) body.runtime))
              Φ :=
      hsubst.symm ▸ hbody
    rw [Binder.runtime_of_name_none hname]
    simpa [Runtime.Subst.updateBinder] using hbody'
  | some x =>
    simp [hname] at hΨ_e
    set base := x
    set x' := Fresh.freshNumbers base st₁.decls.allNames
    set v : FOL.Const := ⟨x', .value⟩
    have _hvty : v.sort = .value := rfl
    have hfresh : v.name ∉ st₁.decls.allNames :=
      Fresh.freshNumbers_not_mem base st₁.decls.allNames
    set st₂ : TransState :=
      { decls := st₁.decls.addConst v,
        asserts := (Formula.eq .value (.const (.uninterpreted v.name .value)) se) :: st₁.asserts,
        owns := st₁.owns }
    set ρ_body := ρ_e.updateConst .value v.name v_e
    set γ_body : Runtime.Subst := Runtime.Subst.update γ x v_e
    suffices st₂.sl Θ ρ_body ∗
        (TinyML.ValHasType Θ v_e e.ty ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R)) ⊢
          wp (reg.wpCtx) (body.runtime.subst γ_body) Φ by
      have hsubst := Runtime.Expr.subst_remove'_updateBinder body.runtime γ (.named x) v_e
      have hbody' : st₂.sl Θ ρ_body ∗
            (TinyML.ValHasType Θ v_e e.ty ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R)) ⊢
              wp (reg.wpCtx)
                (Runtime.Expr.subst
                  (Runtime.Subst.updateBinder (.named x) v_e Runtime.Subst.id)
                  (Runtime.Expr.subst (γ.remove' (.named x)) body.runtime))
                Φ :=
        hsubst.symm ▸ this
      have hinterp_eq : SpatialContext.interp Θ ρ_e.env st₁.owns ⊢ SpatialContext.interp Θ ρ_body.env st₁.owns :=
        (SpatialContext.interp_env_agree Θ (VerifM.eval.wf hΨ_e).ownsWf
          (Env.agreeOn_update_fresh_const hfresh)).1
      rw [Binder.runtime_of_name_some hname]
      exact (sep_mono_l hinterp_eq).trans <|
        by simpa [st₂, γ_body, base, Runtime.Subst.updateBinder, Runtime.Subst.update, Runtime.Subst.id]
          using hbody'
    have hagreeOn_body_e : Env.agreeOn st₁.decls ρ_e.env ρ_body.env :=
      Env.agreeOn_update_fresh_const hfresh
    have hΨ_body : (compile reg Θ Δ_spec (Finmap.erase x S) ((x, v) :: B) (Γ.extend x e.ty) body).eval st₂ ρ_body Ψ := by
      have hdecl_eval := VerifM.eval_bind _ _ _ _ hΨ_e
      have hdecl := VerifM.eval_decl hdecl_eval
      have h := hdecl v_e
      obtain h := VerifM.eval_bind _ _ _ _ h
      obtain h := VerifM.eval_assumePure h
      apply h
      · have hstwf : st₁.decls.wf := (VerifM.eval.wf hdecl_eval).namesDisjoint
        simpa [v] using
          (Formula.eq_wfIn_addConst_of_fresh (Δ := st₁.decls) (c := v) hstwf hse_wf hfresh)
      · simp only [Formula.eval, Term.eval, Const.denote]
        have : v_e = Term.eval ρ_body.env se := by
          rw [Term.eval_env_agree hse_wf (Env.agreeOn_symm hagreeOn_body_e)]
          exact heval_e.symm
        simpa [ρ_body, Env.updateConst] using this
    have hbwf₂ : Bindings.wfIn ((x, v) :: B) st₂.decls := Bindings.wfIn_cons hbwf_e
    have hρ_agree : Env.agreeOn (Signature.ofConsts (B.map Prod.snd)) ρ_body.env ρ.env := by
      constructor
      · intro y hy
        cases hy
      · constructor
        · intro y' hy'
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy'
          exact ((hagreeOn_e.2.1 p.2 (hbwf p hp)).trans
            (hagreeOn_body_e.2.1 p.2 (hbwf_e p hp))).symm
        · constructor
          · intro z hz; cases hz
          · constructor
            · intro z hz; cases hz
            · constructor
              · intro z hz; cases hz
              · intro z hz; cases hz
    have hρ_body_lookup : ρ_body.env.consts .value v.name = v_e := by
      simp [ρ_body, VerifM.Env.updateConst, Env.updateConst]
    have hagree_body : Bindings.agreeOnLinked ((x, v) :: B) ρ_body.env γ_body := by
      have h := Bindings.agreeOnLinked_cons (x := x) (γ := γ) hagree hρ_agree (hvty := (rfl : v.sort = .value))
      rwa [hρ_body_lookup] at h
    have hres :
        st₂.sl Θ ρ_body ∗
          (TinyML.ValHasType Θ v_e e.ty ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R)) ⊢
            st₂.sl Θ ρ_body ∗
              (SpecMap.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec (Finmap.erase x S) γ_body ∗
                Bindings.typedSubst Θ ((x, v) :: B) (Γ.extend x e.ty) γ_body ∗ R) := by
      iintro ⟨Howns, Hve, □HS, □HT, HR⟩
      isplitl [Howns]
      · iexact Howns
      · isplitr [Hve HR]
        · iapply (SpecMap.satisfiedBy_erase (Θ := Θ) (S := S) (γ := γ) (x := x) (v := v_e))
          iexact HS
        · isplitl [Hve]
          · iapply (Bindings.typedSubst_cons (Θ := Θ) (B := B) (Γ := Γ) (γ := γ)
              (x := x) (v := v) (te := e.ty) (w := v_e))
            · iexact HT
            · iexact Hve
          · iexact HR
    have hspecInv_e := specInvariants_mono hΔspec hρspec hdecls_e hagreeOn_e
    have hspecInv_body := specInvariants_mono hspecInv_e.1 hspecInv_e.2
      (Signature.Subset.subset_addConst st₁.decls v) hagreeOn_body_e
    refine hres.trans <| ihBody Θ R (Finmap.erase x S) ((x, v) :: B) (Γ.extend x e.ty) st₂ ρ_body γ_body Δ_spec ρ_spec _ _
      (VerifM.eval.decls_grow ρ_body hΨ_body) hagree_body hbwf₂ (SpecMap.wfIn_erase hSwf) hΔwf hΔvars hspecInv_body.1 hspecInv_body.2 hΔreg hρreg ?_
    intro v' ρ' st' se' hΨ hs hw
    obtain ⟨_, _, hΨ'⟩ := hΨ
    exact hpost v' ρ' st' se' hΨ' hs hw

theorem compileIfThenElse_correct (reg : Verifier.Registry) (cond thn els : Expr) (ty : TinyML.Typ)
    (ihCond : correctExpr reg cond) (ihThn : correctExpr reg thn) (ihEls : correctExpr reg els) :
    correctExpr reg (.ifThenElse cond thn els ty) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  simp only [Expr.ty] at hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  have heval_cond : (compile reg Θ Δ_spec S B Γ cond).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  have hstart :
      st.sl Θ ρ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) ⊢
        st.sl Θ ρ ∗
          (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗
            (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R)) :=
    Helpers.ctx_dup reg Θ Δ_spec ρ_spec S B Γ st ρ γ R
  refine SpatialContext.wp_bind_if <| hstart.trans <|
    ihCond Θ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) S B Γ st ρ γ Δ_spec ρ_spec _ _
      (VerifM.eval.decls_grow ρ heval_cond) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
  intro v_c ρ_c st₁ sc hΨ_c hsc_wf heval_c
  obtain ⟨hdecls_c, hagreeOn_c, hΨ_c⟩ := hΨ_c
  have hagree_c := Bindings.agreeOnLinked_env_agree hagree hagreeOn_c hbwf
  have hbwf_c : B.wfIn st₁.decls := fun p hp => hdecls_c.consts _ (hbwf p hp)
  have hspecInv_c := specInvariants_mono hΔspec hρspec hdecls_c hagreeOn_c
  obtain ⟨hcond_bool, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
  obtain ⟨hthn_ty, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
  obtain ⟨hels_ty, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
  have heval_branches : (VerifM.all [true, false]).eval st₁ ρ_c _ := VerifM.eval_bind _ _ _ _ hΨ_c
  have hall := VerifM.eval_all heval_branches
  have htrue := hall true (by simp)
  have hfalse := hall false (by simp)
  have hwf_ne : (Formula.not (Formula.eq .value sc (.unop .ofBool (.const (.b false))))).wfIn st₁.decls := by
    simp only [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, _root_.and_true]
    exact hsc_wf
  have hwf_eq : (Formula.eq .value sc (.unop .ofBool (.const (.b false) : Term .bool))).wfIn st₁.decls := by
    simp only [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, _root_.and_true]
    exact hsc_wf
  have htrue_cont := VerifM.eval_assumePure (VerifM.eval_bind _ _ _ _ htrue)
  have hfalse_cont := VerifM.eval_assumePure (VerifM.eval_bind _ _ _ _ hfalse)
  let φ_eq : Formula := .eq .value sc (.unop .ofBool (.const (.b false) : Term .bool))
  let st_thn : TransState := { st₁ with asserts := φ_eq.not :: st₁.asserts }
  let st_els : TransState := { st₁ with asserts := φ_eq :: st₁.asserts }
  have hbool_cases_bool :
      st₁.sl Θ ρ_c ∗
          (TinyML.ValHasType Θ v_c .bool ∗
            (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R)) ⊢
        st₁.sl Θ ρ_c ∗ iprop(⌜v_c = .bool false ∨ v_c = .bool true⌝) ∗
          (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) := by
    iintro ⟨Howns, Hv, □HS, □HT, HR⟩
    ihave Hv_bool := (TinyML.ValHasType.bool Θ v_c).1 $$ Hv
    icases Hv_bool with ⟨%b, %hv⟩
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · exact pure_intro (by subst hv; cases b <;> simp)
      · isplitl []
        · iexact HS
        · isplitl []
          · iexact HT
          · iexact HR
  have hbool_cases :
      st₁.sl Θ ρ_c ∗ (TinyML.ValHasType Θ v_c cond.ty ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R)) ⊢
        st₁.sl Θ ρ_c ∗ iprop(⌜v_c = .bool false ∨ v_c = .bool true⌝) ∗
          (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) := by
    simpa [hcond_bool] using hbool_cases_bool
  refine hbool_cases.trans ?_
  istart
  iintro ⟨Howns, Hbool, □HS, □HT, HR⟩
  icases Hbool with %hbool
  rcases hbool with hfalse_val | htrue_val
  · subst hfalse_val
    have heval_els : (compile reg Θ Δ_spec S B Γ els).eval st_els ρ_c Ψ :=
      hfalse_cont hwf_eq (by
        simp only [Formula.eval, Term.eval, UnOp.eval, Const.denote]
        exact heval_c)
    have hwp :
        st_els.sl Θ ρ_c ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) ⊢
          wp (reg.wpCtx) (.ifThenElse (.val (.bool false)) (thn.runtime.subst γ) (els.runtime.subst γ)) Φ :=
      SpatialContext.wp_if_false
        (thn := thn.runtime.subst γ) (els := els.runtime.subst γ) <|
        ihEls Θ R S B Γ st_els ρ_c γ Δ_spec ρ_spec Ψ Φ heval_els hagree_c hbwf_c hSwf hΔwf hΔvars hspecInv_c.1 hspecInv_c.2 hΔreg hρreg
          (fun v ρ' st' se hΨ hs hw =>
            by simpa [hels_ty] using hpost v ρ' st' se hΨ hs hw)
    have hctx :
        st₁.sl Θ ρ_c ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) ⊢
          st_els.sl Θ ρ_c ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) := by
      simp [st_els, TransState.sl]
    iapply (hctx.trans hwp)
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · iexact HS
      · isplitl []
        · iexact HT
        · iexact HR
  · subst htrue_val
    have heval_ne : sc.eval ρ_c.env ≠ Runtime.Val.bool false := by
      rw [heval_c]
      simp
    have heval_thn : (compile reg Θ Δ_spec S B Γ thn).eval st_thn ρ_c Ψ :=
      htrue_cont hwf_ne (by
        simp only [Formula.eval, Term.eval, UnOp.eval, Const.denote]
        exact heval_ne)
    have hwp :
        st_thn.sl Θ ρ_c ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) ⊢
          wp (reg.wpCtx) (.ifThenElse (.val (.bool true)) (thn.runtime.subst γ) (els.runtime.subst γ)) Φ :=
      SpatialContext.wp_if_true
        (thn := thn.runtime.subst γ) (els := els.runtime.subst γ) <|
        ihThn Θ R S B Γ st_thn ρ_c γ Δ_spec ρ_spec Ψ Φ heval_thn hagree_c hbwf_c hSwf hΔwf hΔvars hspecInv_c.1 hspecInv_c.2 hΔreg hρreg
          (fun v ρ' st' se hΨ hs hw =>
            by simpa [hthn_ty] using hpost v ρ' st' se hΨ hs hw)
    have hctx :
        st₁.sl Θ ρ_c ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) ⊢
          st_thn.sl Θ ρ_c ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R) := by
      simp [st_thn, TransState.sl]
    iapply (hctx.trans hwp)
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · iexact HS
      · isplitl []
        · iexact HT
        · iexact HR

theorem compileTuple_correct (reg : Verifier.Registry) (es : List Expr)
    (ihEs : correctExprs reg es) :
    correctExpr reg (.tuple es) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  simp only [Expr.ty] at hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst, List.map_map]
  simp only [compile] at heval
  have heval_es : (compileExprs reg Θ Δ_spec S B Γ es).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_tuple <| ihEs Θ R S B Γ st ρ γ Δ_spec ρ_spec _ _
    (VerifM.eval.decls_grow ρ heval_es) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
  intro vs ρ' st' terms hΨ hwf_terms heval_terms
  obtain ⟨_, _, hΨ⟩ := hΨ
  obtain hΨ := VerifM.eval_ret hΨ
  have heval_tuple : (Term.unop .ofValList (Terms.toValList terms)).eval ρ'.env = Runtime.Val.tuple vs := by
    simp [Term.eval, UnOp.eval, Terms.toValList_eval heval_terms]
  have hwf_tuple : (Term.unop UnOp.ofValList (Terms.toValList terms)).wfIn st'.decls := by
    simp only [Term.wfIn]
    exact ⟨trivial, Terms.toValList_wfIn hwf_terms⟩
  refine SpatialContext.wp_tuple ?_
  have hstep :
      st'.sl Θ ρ' ∗ TinyML.ValsHaveTypes Θ vs (es.map Expr.ty) ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R) ⊢
        st'.sl Θ ρ' ∗ TinyML.ValHasType Θ (.tuple vs) (.tuple (es.map Expr.ty)) ∗ R := by
    iintro ⟨Howns, Hvals, □HS, HR⟩
    isplitl [Howns]
    · iexact Howns
    · isplitl [Hvals]
      · iapply (TinyML.ValHasType.tuple Θ (.tuple vs) (es.map Expr.ty)).2
        iexists vs
        isplitr
        · ipure_intro; rfl
        · iexact Hvals
      · iexact HR
  exact hstep.trans <|
    hpost (Runtime.Val.tuple vs) ρ' st' (.unop .ofValList (Terms.toValList terms))
      hΨ hwf_tuple heval_tuple

theorem compileApp_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (fn : Expr) (args : List Expr) (aty : TinyML.Typ)
    (ihArgs : correctExprs reg args) :
    correctExpr reg (.app fn args aty) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  simp only [Expr.ty] at hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst, List.map_map]
  cases fn with
  | var f fty =>
    simp only [compile] at heval
    obtain ⟨spec, hlookup, heval⟩ := VerifM.eval_bind_expectSome heval
    have heval_args : (compileExprs reg Θ Δ_spec S B Γ args).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine SpecMap.project (wctx := reg.wpCtx)
      (P := st.sl Θ ρ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R)) Θ Δ_spec ρ_spec S γ ?_ hlookup ?_
    · istart
      iintro ⟨_, □HS, _⟩
      iexact HS
    · intro fval hγf
      simp [Expr.runtime, Runtime.Expr.subst, hγf]
      refine SpatialContext.wp_bind_app ?_
      have hctx :
          spec.isPrecondFor (reg.wpCtx) Θ Δ_spec ρ_spec fval ∗
              (st.sl Θ ρ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B Γ γ ∗ R)) ⊢
            st.sl Θ ρ ∗
              (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗
                Bindings.typedSubst Θ B Γ γ ∗ (spec.isPrecondFor (reg.wpCtx) Θ Δ_spec ρ_spec fval ∗ R)) := by
        istart
        iintro ⟨□Hspec, Howns, □HS, □HT, HR⟩
        isplitl [Howns]
        · iexact Howns
        · isplitl []
          · iexact HS
          · isplitl []
            · iexact HT
            · isplitl []
              · iexact Hspec
              · iexact HR
      refine hctx.trans <|
        ihArgs Θ (spec.isPrecondFor (reg.wpCtx) Θ Δ_spec ρ_spec fval ∗ R) S B Γ st ρ γ Δ_spec ρ_spec _ _
          (VerifM.eval.decls_grow ρ heval_args) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
      intro vs ρ_args st_args sargs hΨ_args hsargs_wf heval_sargs
      obtain ⟨hdecls_args, hagreeOn_args, hΨ_args⟩ := hΨ_args
      let typedArgs := (args.map Expr.ty).zip sargs
      have hlen_sargs : sargs.length = vs.length := by
        simpa [Terms.Eval] using List.Forall₂.length_eq heval_sargs
      obtain ⟨hret_eq, hΨ_args⟩ := VerifM.eval_bind_expectEq hΨ_args
      obtain ⟨_, hΨ_args⟩ := VerifM.eval_bind_expectEq hΨ_args
      have hΔspec_args : Δ_spec.Subset st_args.decls := hΔspec.trans hdecls_args
      have hst_args_wf : st_args.decls.wf := (VerifM.eval.wf hΨ_args).namesDisjoint
      have hwf_pred : spec.pred.wfIn ((Δ_spec.declVars (FiniteSubst.base Δ_spec).dom).declVars (Spec.argVars spec.args)) := by
        simpa [FiniteSubst.base, Signature.declVars] using hSwf f spec hlookup
      have hbase_wf : (FiniteSubst.base Δ_spec).wf Δ_spec st_args.decls :=
        FiniteSubst.base_wfIn hΔspec_args hΔwf hst_args_wf hΔvars
      have htypedArgs_wf : ∀ p ∈ typedArgs, p.2.wfIn st_args.decls := by
        intro p hp
        have hp'' : p.2 ∈ sargs := (List.of_mem_zip hp).2
        exact hsargs_wf _ hp''
      have hcall_eval : VerifM.eval (Spec.call Θ (FiniteSubst.base Δ_spec) spec typedArgs) st_args ρ_args
          (fun p st' ρ' => VerifM.eval (pure p.2) st' ρ' Ψ) := VerifM.eval_bind _ _ _ _ hΨ_args
      have hcall := Spec.call_correct Θ spec Δ_spec (FiniteSubst.base Δ_spec) typedArgs st_args ρ_args
        (fun p st' ρ' => VerifM.eval (pure p.2) st' ρ' Ψ) Φ R
        hwf_pred
        hbase_wf htypedArgs_wf hcall_eval
        (fun v st' ρ' t hΨ hwf heval => by
          have h := hpost v ρ' st' t (VerifM.eval_ret hΨ) hwf heval
          rw [← hret_eq] at h
          iintro H
          icases H with ⟨Howns', Hrest⟩
          icases Hrest with ⟨HR', Hty⟩
          iapply h
          isplitl [Howns']
          · iexact Howns'
          · isplitl [Hty]
            · iexact Hty
            · iexact HR')
      obtain ⟨hsub_ty, happly⟩ := hcall
      refine SpatialContext.wp_val ?_
      unfold Spec.isPrecondFor
      istart
      iintro ⟨Howns, Hvals, □HS, □Hspec, HR⟩
      iintuitionistic Hvals
      ihave Hlen := TinyML.ValsHaveTypes.length_eq $$ Hvals
      ipure Hlen
      have hlen_typed : (args.map Expr.ty).length = sargs.length := by
        rw [← Hlen]; exact hlen_sargs.symm
      have hsub_ty' : @TinyML.Typ.SubList Θ (args.map Expr.ty) (spec.args.map Prod.snd) := by
        simpa [typedArgs, List.map_fst_zip (Nat.le_of_eq hlen_typed)] using hsub_ty
      have heval_sargs_map : typedArgs.map (fun p => p.2.eval ρ_args.env) = vs := by
        have hsnd :
            List.map Prod.snd ((List.map Expr.ty args).zip sargs) = sargs := by
          simpa using
            (List.map_snd_zip (l₁ := List.map Expr.ty args) (l₂ := sargs)
              (Nat.le_of_eq hlen_typed.symm))
        calc
          typedArgs.map (fun p => p.2.eval ρ_args.env)
              = sargs.map (fun t => t.eval ρ_args.env) := by
                  simpa [typedArgs, List.map_map] using
                    congrArg (List.map (fun t => t.eval ρ_args.env)) hsnd
          _ = vs := Terms.Eval.map_eval heval_sargs
      have hlen_vs : vs.length = (spec.args.map Prod.snd).length := by
        have := hsub_ty'.length_eq
        rw [Hlen]; exact this
      have happly' :
          st_args.sl Θ ρ_args ∗ R ⊢
            PredTrans.apply Θ (fun r => TinyML.ValHasType Θ r spec.retTy -∗ Φ r) spec.pred
              (Spec.argsEnv ρ_args spec.args vs) := by
        rw [heval_sargs_map] at happly
        exact happly
      have hagree_ρ_args : VerifM.Env.agreeOn Δ_spec ρ_spec ρ_args :=
        VerifM.Env.agreeOn_trans hρspec (VerifM.Env.agreeOn_mono hΔspec hagreeOn_args)
      ispecialize Hspec $$ %ρ_args
      ispecialize Hspec $$ %Φ
      ispecialize Hspec $$ %vs
      iapply Hspec
      · ipure_intro
        exact hagree_ρ_args
      · iapply (TinyML.ValsHaveTypes.sub hsub_ty')
        iexact Hvals
      · iapply happly'
        isplitl [Howns]
        · iexact Howns
        · iexact HR
  | prim n fty =>
    simp only [compile] at heval
    obtain ⟨i, hilookup, heval⟩ := VerifM.eval_bind_expectSome heval
    obtain ⟨hret_eq, heval⟩ := VerifM.eval_bind_expectEq heval
    have heval_args : (compileExprs reg Θ Δ_spec S B Γ args).eval st ρ _ :=
      VerifM.eval_bind _ _ _ _ heval
    have hi_mem : i ∈ reg := Verifier.Registry.mem_of_lookup? hilookup
    have hbridge := Verifier.Registry.Sound.get hSound hi_mem
    simp only [Expr.runtime, Runtime.Expr.subst_val]
    refine SpatialContext.wp_bind_app ?_
    refine ihArgs Θ R S B Γ st ρ γ Δ_spec ρ_spec _ _
      (VerifM.eval.decls_grow ρ heval_args) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
    intro vs ρ_args st_args sargs hΨ_args hsargs_wf heval_sargs
    obtain ⟨hdecls_args, hagreeOn_args, hΨ_args⟩ := hΨ_args
    let spec := i.spec
    let typedArgs := (args.map Expr.ty).zip sargs
    have hlen_sargs : sargs.length = vs.length := by
      simpa [Terms.Eval] using List.Forall₂.length_eq heval_sargs
    have hΔspec_args : Δ_spec.Subset st_args.decls := hΔspec.trans hdecls_args
    have hst_args_wf : st_args.decls.wf := (VerifM.eval.wf hΨ_args).namesDisjoint
    have hwf_pred :
        spec.pred.wfIn ((Δ_spec.declVars (FiniteSubst.base Δ_spec).dom).declVars
          (Spec.argVars spec.args)) := by
      simpa [spec, FiniteSubst.base, Signature.declVars] using
        hbridge.specWf Δ_spec (hΔreg i hi_mem) hΔwf
    have hbase_wf : (FiniteSubst.base Δ_spec).wf Δ_spec st_args.decls :=
      FiniteSubst.base_wfIn hΔspec_args hΔwf hst_args_wf hΔvars
    have htypedArgs_wf : ∀ p ∈ typedArgs, p.2.wfIn st_args.decls := by
      intro p hp
      have hp'' : p.2 ∈ sargs := (List.of_mem_zip hp).2
      exact hsargs_wf _ hp''
    have hcall_eval : VerifM.eval (Spec.call Θ (FiniteSubst.base Δ_spec) spec typedArgs) st_args ρ_args
        (fun p st' ρ' => VerifM.eval (pure p.2) st' ρ' Ψ) := VerifM.eval_bind _ _ _ _ hΨ_args
    have hcall := Spec.call_correct Θ spec Δ_spec (FiniteSubst.base Δ_spec) typedArgs st_args ρ_args
      (fun p st' ρ' => VerifM.eval (pure p.2) st' ρ' Ψ) Φ R
      hwf_pred hbase_wf htypedArgs_wf hcall_eval
      (fun v st' ρ' t hΨ hwf heval => by
        have hret_eq' : spec.retTy = aty := by
          simpa [spec, Verifier.Intrinsic.resultTy] using hret_eq
        have h := hpost v ρ' st' t (VerifM.eval_ret hΨ) hwf heval
        rw [← hret_eq'] at h
        iintro H
        icases H with ⟨Howns', Hrest⟩
        icases Hrest with ⟨HR', Hty⟩
        iapply h
        isplitl [Howns']
        · iexact Howns'
        · isplitl [Hty]
          · iexact Hty
          · iexact HR')
    obtain ⟨hsub_ty, happly⟩ := hcall
    refine SpatialContext.wp_val ?_
    refine BIBase.Entails.trans ?_ wp.prim
    show _ ⊢ (reg.wpCtx) n vs Φ
    have hctx_eq : (reg.wpCtx) n vs Φ = i.toWp vs Φ := by
      simp only [Verifier.Registry.wpCtx, hilookup]
    rw [hctx_eq]
    istart
    iintro ⟨Howns, Hvals, _HS, HR⟩
    iintuitionistic Hvals
    ihave Hlen := TinyML.ValsHaveTypes.length_eq $$ Hvals
    ipure Hlen
    have hlen_typed : (args.map Expr.ty).length = sargs.length := by
      rw [← Hlen]; exact hlen_sargs.symm
    have hsub_ty' : @TinyML.Typ.SubList Θ (args.map Expr.ty) i.argTysList := by
      have hspec_snd : i.specArgs.map Prod.snd = i.argTysList := rfl
      have hfst : typedArgs.map Prod.fst = args.map Expr.ty := by
        simpa [typedArgs] using
          (List.map_fst_zip (l₁ := args.map Expr.ty) (l₂ := sargs)
            (Nat.le_of_eq hlen_typed))
      simpa [spec, hspec_snd, hfst] using hsub_ty
    have heval_sargs_map : typedArgs.map (fun p => p.2.eval ρ_args.env) = vs := by
      have hsnd :
          List.map Prod.snd ((List.map Expr.ty args).zip sargs) = sargs := by
        simpa using
          (List.map_snd_zip (l₁ := List.map Expr.ty args) (l₂ := sargs)
            (Nat.le_of_eq hlen_typed.symm))
      calc
        typedArgs.map (fun p => p.2.eval ρ_args.env)
            = sargs.map (fun t => t.eval ρ_args.env) := by
                simpa [typedArgs, List.map_map] using
                  congrArg (List.map (fun t => t.eval ρ_args.env)) hsnd
        _ = vs := Terms.Eval.map_eval heval_sargs
    have happly' :
        st_args.sl Θ ρ_args ∗ R ⊢
          PredTrans.apply Θ (fun r => TinyML.ValHasType Θ r i.resultTy -∗ Φ r) i.spec.pred
            (Spec.argsEnv ρ_args i.specArgs vs) := by
      rw [heval_sargs_map] at happly
      simpa [spec, Verifier.Intrinsic.specArgs] using happly
    have hagree_ρ_args : VerifM.Env.agreeOn Δ_spec ρ_spec ρ_args :=
      VerifM.Env.agreeOn_trans hρspec (VerifM.Env.agreeOn_mono hΔspec hagreeOn_args)
    have hρ_args_reg : ρ_args.env.respects i.folSym :=
      Env.respects_of_agreeOn_extendWithSym (hρreg i hi_mem) (hΔreg i hi_mem) hagree_ρ_args
    iapply (show
        TinyML.ValsHaveTypes Θ vs i.argTysList ∗
          PredTrans.apply Θ (fun r => TinyML.ValHasType Θ r i.resultTy -∗ Φ r) i.spec.pred
            (Spec.argsEnv ρ_args i.specArgs vs) ⊢ i.toWp vs Φ from
        hbridge.bridge Θ vs ρ_args Φ hρ_args_reg)
    isplitl [Hvals]
    · iapply (TinyML.ValsHaveTypes.sub hsub_ty')
      iexact Hvals
    · iapply happly'
      isplitl [Howns]
      · iexact Howns
      · iexact HR
  | _ =>
    simp only [compile] at heval
    exact (VerifM.eval_fatal heval).elim

theorem compileMatch_correct (reg : Verifier.Registry) (scrut : Expr) (branches : List (Binder × Expr)) (ty : TinyML.Typ)
    (ihScrut : correctExpr reg scrut) (ihBranches : correctBranches reg branches) :
    correctExpr reg (.match_ scrut branches ty) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  simp only [Expr.ty] at hpost
  unfold Expr.runtime
  simp only [Expr.branchListRuntime_eq_map, Runtime.Expr.subst, List.map_map]
  simp only [compile] at heval
  have heval_scrut : (compile reg Θ Δ_spec S B Γ scrut).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_match <| BIBase.Entails.trans ?_ <|
    ihScrut Θ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗ R) S B Γ st ρ γ Δ_spec ρ_spec _ _
      (VerifM.eval.decls_grow ρ heval_scrut) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
  · exact Helpers.ctx_dup reg Θ Δ_spec ρ_spec S B Γ st ρ γ R
  intro v_scrut ρ_scrut st_scrut se_scrut hΨ_scrut hse_wf heval_se
  obtain ⟨hdecls_scrut, hagreeOn_scrut, hΨ_scrut⟩ := hΨ_scrut
  cases hscrut_ty : scrut.ty with
  | prim _ | arrow _ _ | ref _ | owned _ | empty | value | tuple _ | tvar _ | named _ _ =>
    simp only [hscrut_ty] at hΨ_scrut
    exact (VerifM.eval_fatal hΨ_scrut).elim
  | sum ts =>
    simp [hscrut_ty] at hΨ_scrut
    by_cases hlen : ts.length ≠ branches.length
    · simp [hlen] at hΨ_scrut
      exact (VerifM.eval_fatal hΨ_scrut).elim
    · push_neg at hlen
      by_cases htys : ∀ br ∈ branches, br.2.ty = ty
      · have hΨ_scrut' :
            (do
              let i ← VerifM.all (List.range (compileBranches reg Θ Δ_spec S B Γ se_scrut ts branches 0).length)
              match (compileBranches reg Θ Δ_spec S B Γ se_scrut ts branches 0)[i]? with
              | some m => m
              | none => VerifM.fatal "match branch index out of range").eval st_scrut ρ_scrut Ψ := by
          simpa [if_pos hlen, if_pos htys] using hΨ_scrut
        have hcb := compileBranches_length_get reg Θ Δ_spec S B Γ se_scrut ts branches 0
        have hactions_len := hcb.1
        have heval_all := VerifM.eval_bind _ _ _ _ hΨ_scrut'
        have hall := VerifM.eval_all heval_all
        have hagree_scrut := Bindings.agreeOnLinked_env_agree hagree hagreeOn_scrut hbwf
        have hbwf_scrut : B.wfIn st_scrut.decls := fun p hp => hdecls_scrut.consts _ (hbwf p hp)
        exact (by
          iintro ⟨Hsl, Hscrut, □HS, □HT, HR⟩
          ihave Hscrut_sum := (TinyML.ValHasType.sum Θ v_scrut ts).1 $$ Hscrut
          icases Hscrut_sum with ⟨%tag, %v_payload, %hval_eq, Hsum⟩
          ihave %htag_bound := TinyML.ValSumRel.bound $$ Hsum
          have htag_branches : tag < branches.length := hlen ▸ htag_bound
          have htag_range : tag ∈ List.range (compileBranches reg Θ Δ_spec S B Γ se_scrut ts branches 0).length := by
            rw [hactions_len]
            exact List.mem_range.mpr htag_branches
          have heval_tag := hall tag htag_range
          have hcb_get := hcb.2 tag htag_branches
          simp [hcb_get, show branches[tag]? = some branches[tag] from
            List.getElem?_eq_some_iff.mpr ⟨htag_branches, rfl⟩] at heval_tag
          have hget : ts[tag]? = some (ts[tag]?.getD .value) := by
            rw [List.getElem?_eq_getElem htag_bound]
            simp
          have hspecInv_scrut := specInvariants_mono hΔspec hρspec hdecls_scrut hagreeOn_scrut
          have hbranch_wp := ihBranches Θ R S B Γ se_scrut ts.length ts 0
            st_scrut ρ_scrut γ Δ_spec ρ_spec Ψ Φ
            hagree_scrut hbwf_scrut hSwf hΔwf hΔvars hspecInv_scrut.1 hspecInv_scrut.2 hΔreg hρreg hse_wf
            (fun j hj v ρ' st' se hΨ hse_wf hse_eval => by
              iintro ⟨Hsl, Hv, □HS, HR⟩
              iapply (hpost v ρ' st' se hΨ hse_wf hse_eval)
              isplitl [Hsl]
              · iexact Hsl
              · isplitl [Hv]
                · rw [← htys (branches[j]) (List.getElem_mem _)]
                  iexact Hv
                · iexact HR)
            tag htag_branches (by simpa [Nat.zero_add] using heval_tag)
          have hsc_eval : se_scrut.eval ρ_scrut.env = Runtime.Val.inj tag ts.length v_payload := by
            exact heval_se.trans hval_eq
          have hbranch_entail :
              st_scrut.sl Θ ρ_scrut ∗
                  TinyML.ValSumRel Θ tag v_payload ts ∗
                    (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗ R) ⊢
                wp (reg.wpCtx)
                  ((Runtime.Expr.subst γ
                        (Runtime.Expr.fix Runtime.Binder.none [branches[tag].1.runtime] branches[tag].2.runtime)).app
                    [Runtime.Expr.val v_payload])
                  Φ := by
            refine BIBase.Entails.trans ?_ (by simpa [Nat.zero_add] using hbranch_wp v_payload ((Nat.zero_add tag).symm ▸ hsc_eval))
            iintro ⟨Hsl, Hsum, □HS, □HT, HR⟩
            isplitl [Hsl]
            · simp only [TransState.sl_eq]
              iexact Hsl
            · isplitl [Hsum]
              · iapply (TinyML.ValSumRel.of_getElem? (Θ := Θ) hget)
                iexact Hsum
              · isplitl []
                · iexact HS
                · isplitl []
                  · iexact HT
                  · iexact HR
          have hmatch_entail :
              st_scrut.sl Θ ρ_scrut ∗
                  TinyML.ValSumRel Θ tag v_payload ts ∗
                    (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗ R) ⊢
                wp (reg.wpCtx)
                  ((Runtime.Expr.val (Runtime.Val.inj tag ts.length v_payload)).match_
                    (List.map (Runtime.Expr.subst γ ∘ fun p =>
                      Runtime.Expr.fix Runtime.Binder.none [p.1.runtime] p.2.runtime) branches))
                  Φ :=
            SpatialContext.wp_match
              (R := st_scrut.sl Θ ρ_scrut ∗
                  TinyML.ValSumRel Θ tag v_payload ts ∗
                    (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ B.typedSubst Θ Γ γ ∗ R))
              (branch :=
                Runtime.Expr.subst γ
                  (Runtime.Expr.fix Runtime.Binder.none [branches[tag].1.runtime] branches[tag].2.runtime))
              (by simpa [Runtime.Expr.subst_fix] using hbranch_entail)
              (by simp [htag_branches])
          rw [hval_eq]
          iapply hmatch_entail
          isplitl [Hsl]
          · iexact Hsl
          · isplitl [Hsum]
            · iexact Hsum
            · isplitl []
              · iexact HS
              · isplitl []
                · iexact HT
                · iexact HR)
      · have hΨ_bad : (VerifM.fatal "match branch type annotation mismatch").eval st_scrut ρ_scrut Ψ := by
          simpa [if_pos hlen, if_neg htys] using hΨ_scrut
        exact (VerifM.eval_fatal hΨ_bad).elim

theorem compileSingleBranch_correct (reg : Verifier.Registry) (binder : Binder) (body : Expr)
    (ihBody : correctExpr reg body) :
    correctBranch reg (binder, body) := by
  intro Θ R S B Γ sc n i ty_i st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hsc_wf hpost payload hsc_eval
  simp only [compileBranch] at heval
  by_cases hty : binder.ty = ty_i
  · have hexpect := VerifM.eval_bind _ _ _ _ heval
    obtain ⟨_, hcont⟩ := VerifM.eval_expectEq hexpect
    have heval_decl := VerifM.eval_bind _ _ _ _ hcont
    have hdecl := VerifM.eval_decl heval_decl
    let hint := binder.name
    let xv := TransState.freshConst hint .value st
    have heval_inst := hdecl payload
    have heval_assume := VerifM.eval_bind _ _ _ _ heval_inst
    have hassume := VerifM.eval_assumePure heval_assume
    let st₁ : TransState := { decls := st.decls.addConst xv, asserts := st.asserts, owns := st.owns }
    let ρ₁ := ρ.updateConst .value xv.name payload
    have hxv_fresh : xv.name ∉ st.decls.allNames :=
      TransState.freshConst_fresh st hint .value
    have hstwf : st.decls.wf := (VerifM.eval.wf heval_decl).namesDisjoint
    have hxv_wf : (Term.const (.uninterpreted xv.name .value)).wfIn st₁.decls :=
      by
        simpa [st₁] using
          (Term.const_wfIn_addConst_of_fresh (Δ := st.decls) (c := xv) hstwf hxv_fresh)
    have hformula_wf : (Formula.eq .value sc
        (.unop (.mkInj i n) (.const (.uninterpreted xv.name .value)))).wfIn st₁.decls := by
      refine ⟨Term.wfIn_mono sc hsc_wf (Signature.Subset.subset_addConst _ _)
        (Signature.wf_addConst hstwf hxv_fresh), trivial, hxv_wf⟩
    have hsc_eval_ρ₁ : sc.eval ρ₁.env = sc.eval ρ.env :=
      Term.eval_env_agree hsc_wf (Env.agreeOn_symm (Env.agreeOn_update_fresh_const hxv_fresh))
    have hformula_eval : Formula.eval ρ₁.env
        (Formula.eq .value sc (.unop (.mkInj i n) (.const (.uninterpreted xv.name .value)))) := by
      simp [Formula.eval, Term.eval, UnOp.eval]
      rw [hsc_eval_ρ₁, hsc_eval]
      simp [ρ₁, Env.updateConst]
    have heval_assumeAll := hassume hformula_wf hformula_eval
    have hxv_eval : (Term.const (.uninterpreted xv.name .value)).eval ρ₁.env = payload := by
      simp [Term.eval, Const.denote, ρ₁, Env.updateConst]
    have hassume_bind₂ := VerifM.eval_bind _ _ _ _ heval_assumeAll
    have hinterp_eq : SpatialContext.interp Θ ρ.env st.owns ⊢ SpatialContext.interp Θ ρ₁.env st.owns :=
      (SpatialContext.interp_env_agree Θ (VerifM.eval.wf heval_decl).ownsWf
        (Env.agreeOn_update_fresh_const hxv_fresh)).1
    have hagreeOn_st : Env.agreeOn st.decls ρ.env ρ₁.env :=
      Env.agreeOn_update_fresh_const hxv_fresh
    -- Extract the type-constraints Prop from the iProp `ValHasType Θ payload ty_i`
    -- assumption, then dispatch into iproof mode to build the final entailment.
    istart
    iintro ⟨Howns, Hpay, □HS, □HT, HR⟩
    iintuitionistic Hpay
    ihave Hcheck := TinyML.typeConstraints_hold (ty := ty_i)
        (t := Term.const (.uninterpreted xv.name .value))
        (ρ := ρ₁.env) (Θ := Θ) (v := payload) hxv_eval $$ Hpay
    ipure Hcheck
    obtain ⟨st₂, hst₂_decls, hst₂_owns, _, heval_body'⟩ := VerifM.eval_assumeAll hassume_bind₂
      (fun φ hφ => TinyML.typeConstraints_wfIn hxv_wf φ hφ)
      (fun φ hφ => Hcheck φ hφ)
    have hst₂_owns_eq : st₂.owns = st.owns := hst₂_owns
    cases hname : binder.name with
    | none =>
      simp [hname] at heval_body'
      have hagree₁ : B.agreeOnLinked ρ₁.env γ :=
        Bindings.agreeOnLinked_env_agree hagree hagreeOn_st hbwf
      have hbwf₁ : B.wfIn st₂.decls := hst₂_decls ▸ fun p hp => List.Mem.tail _ (hbwf p hp)
      have heval_body'' : (compile reg Θ Δ_spec S B (Γ.extendBinder binder ty_i) body).eval st₂ ρ₁ Ψ := by
        simpa [ρ₁, xv, hint, hname] using heval_body'
      have hspecInv₁ := specInvariants_mono hΔspec hρspec
        (Signature.Subset.subset_addConst st.decls xv) hagreeOn_st
      have hBodyWp :
          st₂.sl Θ ρ₁ ∗
              (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ Bindings.typedSubst Θ B (Γ.extendBinder binder ty_i) γ ∗
                (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R)) ⊢
            wp (reg.wpCtx) (body.runtime.subst γ) Φ :=
        ihBody Θ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R) S B (Γ.extendBinder binder ty_i) st₂ ρ₁ γ Δ_spec ρ_spec Ψ Φ
          heval_body'' hagree₁ hbwf₁ hSwf hΔwf hΔvars (hst₂_decls ▸ hspecInv₁.1) hspecInv₁.2
          hΔreg hρreg
          (fun v ρ' st' se hΨ' hs hw => hpost v ρ' st' se hΨ' hs hw)
      rw [Binder.runtime_of_name_none hname]
      simp only [Runtime.Expr.subst_fix]
      refine BIBase.Entails.trans ?_ wp.app_lambda_single
      simp only [Runtime.Subst.removeAll'_cons, Runtime.Subst.removeAll'_nil]
      rw [Runtime.Expr.subst_remove'_updateBinder body.runtime (γ.remove' .none) .none payload]
      simp only [Runtime.Subst.updateBinder, Runtime.Subst.remove'_none]
      refine BIBase.Entails.trans ?_ hBodyWp
      istart
      iintro ⟨⟨⟨⟨Howns, □HS⟩, □HT⟩, HR⟩, □Hpay⟩
      -- spatial: Howns (st.sl Θ ρ), HR; persistent: Hpay, HS, HT
      -- goal: st₂.sl Θ ρ₁ ∗ (S.satisfiedBy ∗ typedSubst extended ∗ (S.satisfiedBy ∗ R))
      isplitl [Howns]
      · have hsl_trans : st.sl Θ ρ ⊢ st₂.sl Θ ρ₁ := by
          simp only [TransState.sl_eq, hst₂_owns_eq]; exact hinterp_eq
        iapply hsl_trans
        iexact Howns
      · isplitl []
        · iexact HS
        · isplitl []
          · -- typedSubst (Γ.extendBinder binder ty_i) γ, with hname = none equals typedSubst Γ γ
            simp only [TinyML.TyCtx.extendBinder, hname]
            iexact HT
          · isplitl []
            · iexact HS
            · iexact HR
    | some x =>
      simp [hname, TinyML.TyCtx.extendBinder] at heval_body'
      have hagreeOn_B : Env.agreeOn (Signature.ofConsts (B.map Prod.snd)) ρ₁.env ρ.env := by
        constructor
        · intro w hw
          cases hw
        · constructor
          · intro c hc
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
            exact (hagreeOn_st.2.1 p.2 (hbwf p hp)).symm
          · constructor
            · intro z hz; cases hz
            · constructor
              · intro z hz; cases hz
              · constructor
                · intro z hz; cases hz
                · intro z hz; cases hz
      have hbwf₂ : Bindings.wfIn ((x, xv) :: B) st₂.decls := hst₂_decls ▸ Bindings.wfIn_cons hbwf
      have hρ₁_lookup : ρ₁.env.consts .value xv.name = payload := by
        simp [ρ₁, VerifM.Env.updateConst, Env.updateConst]
      have hagree₁ : Bindings.agreeOnLinked ((x, xv) :: B) ρ₁.env (Runtime.Subst.update γ x payload) := by
        have h := Bindings.agreeOnLinked_cons (x := x) (v := xv) (γ := γ) hagree hagreeOn_B (hvty := rfl)
        rwa [hρ₁_lookup] at h
      have heval_body'' :
          (compile reg Θ Δ_spec (Finmap.erase x S) ((x, xv) :: B) (Γ.extendBinder binder ty_i) body).eval st₂ ρ₁ Ψ := by
        simpa [ρ₁, xv, hint, TinyML.TyCtx.extendBinder, hname] using heval_body'
      have hspecInv₁ := specInvariants_mono hΔspec hρspec
        (Signature.Subset.subset_addConst st.decls xv) hagreeOn_st
      have hBodyWp :
          st₂.sl Θ ρ₁ ∗
              (SpecMap.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec (Finmap.erase x S) (Runtime.Subst.update γ x payload) ∗
                Bindings.typedSubst Θ ((x, xv) :: B) (Γ.extendBinder binder ty_i) (Runtime.Subst.update γ x payload) ∗
                (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R)) ⊢
            wp (reg.wpCtx) (body.runtime.subst (Runtime.Subst.update γ x payload)) Φ :=
        ihBody Θ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R) (Finmap.erase x S) ((x, xv) :: B) (Γ.extendBinder binder ty_i) st₂ ρ₁
          (Runtime.Subst.update γ x payload) Δ_spec ρ_spec Ψ Φ heval_body'' hagree₁ hbwf₂ (SpecMap.wfIn_erase hSwf)
          hΔwf hΔvars (hst₂_decls ▸ hspecInv₁.1) hspecInv₁.2
          hΔreg hρreg
          (fun v ρ' st' se hΨ' hs hw => hpost v ρ' st' se hΨ' hs hw)
      rw [Binder.runtime_of_name_some hname]
      simp only [Runtime.Expr.subst_fix]
      refine BIBase.Entails.trans ?_ wp.app_lambda_single
      simp only [Runtime.Subst.removeAll'_cons, Runtime.Subst.removeAll'_nil, Runtime.Subst.remove'_none]
      rw [Runtime.Expr.subst_remove'_updateBinder body.runtime γ (.named x) payload]
      simp only [Runtime.Subst.updateBinder]
      refine BIBase.Entails.trans ?_ hBodyWp
      istart
      iintro ⟨⟨⟨⟨Howns, □HS⟩, □HT⟩, HR⟩, □Hpay⟩
      isplitl [Howns]
      · have hsl_trans : st.sl Θ ρ ⊢ st₂.sl Θ ρ₁ := by
          simp only [TransState.sl_eq, hst₂_owns_eq]; exact hinterp_eq
        iapply hsl_trans
        iexact Howns
      · isplitl []
        · -- satisfiedBy for erased S: derive from S.satisfiedBy (persistent)
          iapply (SpecMap.satisfiedBy_erase (Θ := Θ) (S := S) (γ := γ) (x := x) (v := payload))
          iexact HS
        · isplitl [Hpay]
          · -- typedSubst extended for (x :: B) and Γ.extend x ty_i
            simp only [TinyML.TyCtx.extendBinder, hname]
            iapply (Bindings.typedSubst_cons (Θ := Θ) (B := B) (Γ := Γ) (γ := γ)
              (x := x) (v := xv) (te := ty_i) (w := payload))
            · iexact HT
            · iexact Hpay
          · isplitl []
            · iexact HS
            · iexact HR
  · have hexpect := VerifM.eval_bind _ _ _ _ heval
    exact False.elim (hty (VerifM.eval_expectEq hexpect).1)

theorem compileBranchesCons_correct (reg : Verifier.Registry) (b : Binder × Expr) (bs : List (Binder × Expr))
    (ihHead : correctBranch reg b) (ihTail : correctBranches reg bs) :
    correctBranches reg (b :: bs) := by
  intro Θ R S B Γ sc n ts idx st ρ γ Δ_spec ρ_spec Ψ Φ hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hsc_wf hpost j hj
  cases j with
  | zero =>
    simp only [Nat.add_zero, List.getElem_cons_zero]
    intro heval
    exact ihHead Θ R S B Γ sc n idx (ts[idx]?.getD .value) st ρ γ Δ_spec ρ_spec Ψ Φ
      heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hsc_wf (by simpa using hpost 0 hj)
  | succ k =>
    have hk : k < bs.length := by simp at hj; omega
    have hidx : idx + (k + 1) = (idx + 1) + k := by omega
    simp only [hidx, List.getElem_cons_succ]
    exact ihTail Θ R S B Γ sc n ts (idx + 1) st ρ γ Δ_spec ρ_spec Ψ Φ
      hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hsc_wf
      (by
        intro j hj' v ρ' st' se hΨ hse_wf hse_eval htyped
        simpa [Nat.add_assoc] using hpost (j + 1) (by simpa using hj') v ρ' st' se hΨ hse_wf hse_eval htyped)
      k hk

theorem compileExprsCons_correct (reg : Verifier.Registry) (e : Expr) (rest : List Expr)
    (ihE : correctExpr reg e) (ihRest : correctExprs reg rest) :
    correctExprs reg (e :: rest) := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  simp only [compileExprs] at heval
  simp only [List.map, wps_cons]
  have heval_rest : (compileExprs reg Θ Δ_spec S B Γ rest).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine BIBase.Entails.trans ?_ <|
    ihRest Θ (B.typedSubst Θ Γ γ ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R)) S B Γ st ρ γ Δ_spec ρ_spec _ _
      (VerifM.eval.decls_grow ρ heval_rest) hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg ?_
  · iintro ⟨Hsl, □HS, □HT, HR⟩
    isplitl [Hsl]
    · iexact Hsl
    · isplitl []
      · iexact HS
      · isplitl []
        · iexact HT
        · isplitl []
          · iexact HT
          · isplitl []
            · iexact HS
            · iexact HR
  intro vs ρ_vs st_vs rest_terms hΨ_vs hwf_rest heval_rest
  obtain ⟨hdecls_vs, hagreeOn_vs, hΨ_vs⟩ := hΨ_vs
  have hagree_vs : B.agreeOnLinked ρ_vs.env γ :=
    Bindings.agreeOnLinked_env_agree hagree hagreeOn_vs hbwf
  have hbwf_vs : B.wfIn st_vs.decls := fun p hp => hdecls_vs.consts _ (hbwf p hp)
  have heval_e : (compile reg Θ Δ_spec S B Γ e).eval st_vs ρ_vs _ := VerifM.eval_bind _ _ _ _ hΨ_vs
  have hspecInv_vs := specInvariants_mono hΔspec hρspec hdecls_vs hagreeOn_vs
  refine BIBase.Entails.trans ?_ <|
    ihE Θ (TinyML.ValsHaveTypes Θ vs (rest.map Expr.ty) ∗ (S.satisfiedBy (reg.wpCtx) Θ Δ_spec ρ_spec γ ∗ R))
    S B Γ st_vs ρ_vs γ Δ_spec ρ_spec _ _
    (VerifM.eval.decls_grow ρ_vs heval_e) hagree_vs hbwf_vs hSwf hΔwf hΔvars hspecInv_vs.1 hspecInv_vs.2 hΔreg hρreg ?_
  · iintro ⟨Hsl, Hvs, □HS, □HT, □HSpare, HR⟩
    isplitl [Hsl]
    · iexact Hsl
    · isplitl []
      · iexact HS
      · isplitl []
        · iexact HT
        · isplitl [Hvs]
          · iexact Hvs
          · isplitl []
            · iexact HSpare
            · iexact HR
  intro v ρ' st' se hΨ_e hse_wf heval_se
  obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
  have hwfst' : st'.decls.wf := (VerifM.eval.wf hΨ_e).namesDisjoint
  obtain hΨ_e := VerifM.eval_ret hΨ_e
  have hwf_cons : ∀ t ∈ se :: rest_terms, t.wfIn st'.decls := by
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hse_wf
    · exact Term.wfIn_mono _ (hwf_rest t ht) hdecls_e hwfst'
  have heval_cons : Terms.Eval ρ'.env (se :: rest_terms) (v :: vs) :=
    Terms.Eval.cons heval_se
      (Terms.Eval.env_agree
        (fun t ht => hwf_rest t ht)
        hagreeOn_e
        heval_rest)
  exact (by
    iintro ⟨Hsl, Hv, Hvs, □HSpare, HR⟩
    iapply (hpost (v :: vs) ρ' st' (se :: rest_terms) hΨ_e hwf_cons heval_cons)
    isplitl [Hsl]
    · iexact Hsl
    · isplitl [Hv Hvs]
      · iapply (show TinyML.ValHasType Θ v e.ty ∗
            TinyML.ValsHaveTypes Θ vs (rest.map Expr.ty) ⊢
            TinyML.ValsHaveTypes Θ (v :: vs) ((e :: rest).map Expr.ty) by
          simpa [List.map] using
            (TinyML.ValsHaveTypes.cons Θ v vs e.ty (rest.map Expr.ty)).2)
        isplitl [Hv]
        · iexact Hv
        · iexact Hvs
      · isplitl []
        · iexact HSpare
        · iexact HR)

theorem compileBranchesNil_correct (reg : Verifier.Registry) :
    correctBranches reg [] := by
  intro Θ R S B Γ sc n ts idx st ρ γ Δ_spec ρ_spec Ψ Φ hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hsc_wf hpost j hj
  exact absurd hj (Nat.not_lt_zero _)

theorem compileExprsNil_correct (reg : Verifier.Registry) :
    correctExprs reg [] := by
  intro Θ R S B Γ st ρ γ Δ_spec ρ_spec Ψ Φ heval hagree hbwf hSwf hΔwf hΔvars hΔspec hρspec hΔreg hρreg hpost
  simp only [compileExprs] at heval
  simp only [List.map, wps]
  obtain heval := VerifM.eval_ret heval
  iintro ⟨Hsl, □HS, □HT, HR⟩
  iapply (hpost [] ρ st [] heval (by simp) .nil)
  isplitl [Hsl]
  · iexact Hsl
  · isplitl []
    · iapply (show iprop(emp) ⊢ TinyML.ValsHaveTypes Θ [] ([].map Expr.ty) by
        simpa [List.map] using (TinyML.ValsHaveTypes.nil Θ).2)
      iemp_intro
    · isplitl []
      · iexact HS
      · iexact HR


/-! #### Correctness Theorem -/

mutual
theorem compile_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (e : Expr) : correctExpr reg e := by
  cases e with
  | const c =>
    simpa using compileConst_correct reg c
  | var x vty =>
    simpa using compileVar_correct reg x vty
  | prim n ty =>
    simpa using compilePrim_correct reg n ty
  | inj tag arity payload =>
    simpa using compileInj_correct reg tag arity payload (compile_correct reg hSound payload)
  | cast e ty =>
    simpa using compileCast_correct reg e ty (compile_correct reg hSound e)
  | assert e =>
    simpa using compileAssert_correct reg e (compile_correct reg hSound e)
  | fix self args retTy body =>
    simpa using compileFix_correct reg self args retTy body
  | ref owned e =>
    simpa using compileRef_correct reg owned e (compile_correct reg hSound e)
  | deref e ty =>
    simpa using compileDeref_correct reg e ty (compile_correct reg hSound e)
  | store loc val =>
    simpa using compileStore_correct reg loc val (compile_correct reg hSound val) (compile_correct reg hSound loc)
  | unop op e uty =>
    simpa using compileUnop_correct reg op e uty (compile_correct reg hSound e)
  | binop op l r bty =>
    simpa using compileBinop_correct reg op l r bty (compile_correct reg hSound r) (compile_correct reg hSound l)
  | letIn b e body =>
    simpa using compileLetIn_correct reg b e body (compile_correct reg hSound e) (compile_correct reg hSound body)
  | ifThenElse cond thn els ty =>
    simpa using compileIfThenElse_correct reg cond thn els ty
      (compile_correct reg hSound cond) (compile_correct reg hSound thn) (compile_correct reg hSound els)
  | app fn args aty =>
    simpa using compileApp_correct reg hSound fn args aty (compileExprs_correct reg hSound args)
  | tuple es =>
    simpa using compileTuple_correct reg es (compileExprs_correct reg hSound es)
  | match_ scrut branches ty =>
    simpa using compileMatch_correct reg scrut branches ty
      (compile_correct reg hSound scrut) (compileBranches_correct reg hSound branches)

theorem compileBranch_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (branch : Binder × Expr) : correctBranch reg branch := by
  obtain ⟨binder, body⟩ := branch
  simpa using compileSingleBranch_correct reg binder body (compile_correct reg hSound body)

theorem compileBranches_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (branches : List (Binder × Expr)) : correctBranches reg branches := by
  match branches with
  | [] =>
    exact compileBranchesNil_correct reg
  | b :: bs =>
    simpa using compileBranchesCons_correct reg b bs
      (compileBranch_correct reg hSound b) (compileBranches_correct reg hSound bs)

theorem compileExprs_correct (reg : Verifier.Registry) (hSound : Verifier.Registry.Sound reg)
    (es : List Expr) : correctExprs reg es := by
  match es with
  | [] =>
    exact compileExprsNil_correct reg
  | e :: rest =>
    simpa using compileExprsCons_correct reg e rest
      (compile_correct reg hSound e) (compileExprs_correct reg hSound rest)
end

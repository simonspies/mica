import Mica.TinyML.Typed
import Mica.TinyML.Typing
import Mica.TinyML.OpSem
import Mica.SeparationLogic.PrimitiveLaws
import Mica.Verifier.Utils
import Mica.Verifier.Monad
import Mica.Verifier.Assertions
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.Specifications
import Mica.Engine.Driver
import Mica.Base.Fresh
import Mathlib.Data.Finmap

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

/-- Apply `vtail` n times to a vallist term. -/
def vtailN (t : Term .vallist) : Nat → Term .vallist
  | 0     => t
  | n + 1 => .unop .vtail (vtailN t n)

@[simp] theorem vtailN_freeVars (t : Term .vallist) (n : Nat) :
    (vtailN t n).freeVars = t.freeVars := by
  induction n with
  | zero => simp [vtailN]
  | succ n ih => simp [vtailN, Term.freeVars, ih]

theorem vtailN_wfIn {t : Term .vallist} {Δ : Signature} (ht : t.wfIn Δ) (n : Nat) :
    (vtailN t n).wfIn Δ := by
  induction n with
  | zero => simpa [vtailN]
  | succ n ih => simp only [vtailN, Term.wfIn]; exact ⟨trivial, ih⟩

@[simp] theorem vtailN_eval (t : Term .vallist) (ρ : VerifM.Env) :
    ∀ n, (vtailN t n).eval ρ.env = List.drop n (t.eval ρ.env)
  | 0 => by simp [vtailN]
  | n + 1 => by
    simp only [vtailN, Term.eval, UnOp.eval, vtailN_eval t ρ n]
    rw [List.tail_drop]

theorem vhead_vtailN_eval {vs : List Runtime.Val} {w : Runtime.Val} {n : Nat}
    (h : vs[n]? = some w) (t : Term .vallist) (ρ : VerifM.Env) (ht : t.eval ρ.env = vs) :
    (Term.unop .vhead (vtailN t n)).eval ρ.env = w := by
  simp [Term.eval, UnOp.eval, ht, h]

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
    exact vhead_vtailN_eval heval _ ρ (by simp [Term.eval, UnOp.eval, h])
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
  def compile (Θ : TinyML.TypeEnv) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) : Expr → VerifM (Term .value)
    | .const (.int n)  => pure (.unop .ofInt  (.const (.i n)))
    | .const (.bool b) => pure (.unop .ofBool (.const (.b b)))
    | .const .unit     => pure (Term.const .unit)
    | .var x vty => do
        let x' ← VerifM.expectSome s!"undefined variable: {x}" (B.lookup x)
        VerifM.expectEq s!"type annotation mismatch for variable: {x}" (Γ x |>.getD .value) vty
        pure (.const (.uninterpreted x'.name .value))
    | .unop op e uty => do
        let se ← compile Θ S B Γ e
        let ty ← VerifM.expectSome
          s!"type error: operator {repr op} cannot be applied to {repr e.ty}"
          (TinyML.UnOp.typeOf op e.ty)
        VerifM.expectEq "unop type annotation mismatch" ty uty
        let t ← VerifM.expectSome
          s!"unsupported unary operator: {repr op}"
          (compileUnop op se)
        pure t
    | .assert e => do
        let sl ← compile Θ S B Γ e
        VerifM.assert (Formula.eq .bool (Term.unop .toBool sl) (Term.const (.b true)))
        pure (Term.const .unit)
    | .binop op l r bty => do
        let sr ← compile Θ S B Γ r
        let sl ← compile Θ S B Γ l
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
        let se ← compile Θ S B Γ e
        VerifM.expectEq "let type annotation mismatch" b.ty e.ty
        match b.name with
        | none => compile Θ S B Γ body
        | some x =>
          let x' ← VerifM.decl (some x) .value
          VerifM.assume (.pure (Formula.eq .value (.const (.uninterpreted x'.name .value)) se))
          compile Θ (Finmap.erase x S) ((x, x') :: B) (Γ.extend x e.ty) body
    | .ifThenElse cond thn els ty => do
        let sc ← compile Θ S B Γ cond
        VerifM.expectEq "if condition type mismatch" cond.ty .bool
        VerifM.expectEq "if branch type annotation mismatch" thn.ty ty
        VerifM.expectEq "if branch type annotation mismatch" els.ty ty
        let branch ← VerifM.all [true, false]
        if branch then do
          VerifM.assume (.pure (.not (.eq .value sc (.unop .ofBool (.const (.b false))))))
          compile Θ S B Γ thn
        else do
          VerifM.assume (.pure (.eq .value sc (.unop .ofBool (.const (.b false)))))
          compile Θ S B Γ els
    | .app (.var f fty) args aty => do
        let spec ← VerifM.expectSome s!"no spec for function {f}" (S.lookup f)
        let sterms ← compileExprs Θ S B Γ args
        let sargs := (args.map Expr.ty).zip sterms
        VerifM.expectEq "app type annotation mismatch" spec.retTy aty
        VerifM.expectEq "app type annotation mismatch"
          fty (Typed.arrowOfArgs (spec.args.map fun arg => Binder.named arg.1 arg.2) spec.retTy)
        let (_, result) ← Spec.call Θ FiniteSubst.id spec sargs
        pure result
    | .tuple es => do
        let terms ← compileExprs Θ S B Γ es
        pure (.unop .ofValList (Terms.toValList terms))
    | .inj tag arity payload => do
        if tag ≥ arity then VerifM.fatal "inj tag out of range"
        else
          let s ← compile Θ S B Γ payload
          pure (.unop (.mkInj tag arity) s)
    | .match_ scrut branches ty => do
        let sc ← compile Θ S B Γ scrut
        match scrut.ty with
        | .sum ts =>
          if ts.length ≠ branches.length then VerifM.fatal "match arity mismatch"
          else if ∀ br ∈ branches, br.2.ty = ty then do
            let actions := compileBranches Θ S B Γ sc ts branches 0
            let i ← VerifM.all (List.range actions.length)
            match actions[i]? with
            | some m => m
            | none => VerifM.fatal "match branch index out of range"
          else
            VerifM.fatal "match branch type annotation mismatch"
        | _ => VerifM.fatal "match on non-sum type"
    | .cast e ty => do
        let se ← compile Θ S B Γ e
        if TinyML.Typ.sub Θ e.ty ty then pure se
        else VerifM.fatal s!"cast type mismatch"
    | .ref e => do
        let sv ← compile Θ S B Γ e
        let l ← VerifM.decl none .value
        VerifM.assume (.spatial (.pointsTo (.const (.uninterpreted l.name .value)) sv))
        pure (.const (.uninterpreted l.name .value))
    | .deref e ty => do
        VerifM.expectEq "deref type annotation mismatch" e.ty (.ref ty)
        match ty with
        | .int =>
          let sl ← compile Θ S B Γ e
          match ← VerifM.resolve (.own sl) with
          | some sv =>
            VerifM.assert (.unpred .isInt sv)
            VerifM.assume (.spatial (.pointsTo sl sv))
            pure sv
          | none => VerifM.failed "could not resolve points-to assertion"
        | _ => VerifM.fatal "only int references are supported"
    | .store loc val => do
        VerifM.expectEq "store location type mismatch" loc.ty (.ref val.ty)
        let sv ← compile Θ S B Γ val
        let sl ← compile Θ S B Γ loc
        match ← VerifM.resolve (.own sl) with
        | some _ =>
          VerifM.assume (.spatial (.pointsTo sl sv))
          pure (Term.const .unit)
        | none => VerifM.failed "could not resolve points-to assertion"
    | .app _ _ _ | .fix _ _ _ _ => VerifM.fatal "unsupported expression"

  /-- Compile a single match branch: assume the scrutinee is `mkInj i n payload`, then compile the body. -/
  def compileBranch (Θ : TinyML.TypeEnv) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
      (sc : Term .value) (n : Nat) (i : Nat) (ty_i : TinyML.Typ)
      : Binder × Expr → VerifM (Term .value)
    | (binder, body) => do
        VerifM.expectEq "match binder type annotation mismatch" binder.ty ty_i
        let xv ← VerifM.decl binder.name .value
        VerifM.assume (.pure (.eq .value sc (.unop (.mkInj i n) (.const (.uninterpreted xv.name .value)))))
        VerifM.assumeAll (typeConstraints ty_i (.const (.uninterpreted xv.name .value)))
        match binder.name with
        | some x =>
          compile Θ (Finmap.erase x S) ((x, xv) :: B) (Γ.extendBinder binder ty_i) body
        | none =>
          compile Θ S B (Γ.extendBinder binder ty_i) body

  def compileBranches (Θ : TinyML.TypeEnv) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
      (sc : Term .value) (ts : List TinyML.Typ) :
      List (Binder × Expr) → Nat → List (VerifM (Term .value))
    | [], _ => []
    | branch :: rest, i =>
      compileBranch Θ S B Γ sc ts.length i (ts[i]?.getD .value) branch
        :: compileBranches Θ S B Γ sc ts rest (i + 1)

  def compileExprs (Θ : TinyML.TypeEnv) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) : List Expr → VerifM (List (Term .value))
    | [] => pure []
    | e :: es => do
      let rest ← compileExprs Θ S B Γ es
      let se ← compile Θ S B Γ e
      pure (se :: rest)
end

/-! ### Helper lemmas -/

theorem compileBranches_spec (Θ : TinyML.TypeEnv) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (sc : Term .value) (ts : List TinyML.Typ)
    (branches : List (Binder × Expr)) (idx : Nat) :
    (compileBranches Θ S B Γ sc ts branches idx).length = branches.length ∧
    ∀ j, j < branches.length →
      (compileBranches Θ S B Γ sc ts branches idx)[j]? =
        branches[j]?.map (fun branch => compileBranch Θ S B Γ sc ts.length (idx + j) (ts[idx + j]?.getD .value) branch) := by
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


/-- Drop `satisfiedBy` from the resource. -/
theorem SpecMap.satisfiedBy_drop {A R : iProp} {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst} :
    A ∗ (SpecMap.satisfiedBy Θ S γ ∗ R) ⊢ A ∗ R :=
  sep_mono_r sep_elim_r

/-- Duplicate `satisfiedBy` (persistent) in the resource. -/
theorem SpecMap.satisfiedBy_dup {A R : iProp} {Θ : TinyML.TypeEnv} {S : SpecMap} {γ : Runtime.Subst} :
    A ∗ (SpecMap.satisfiedBy Θ S γ ∗ R) ⊢ A ∗ (SpecMap.satisfiedBy Θ S γ ∗ (SpecMap.satisfiedBy Θ S γ ∗ R)) :=
  by
    iintro ⟨HA, □HS, HR⟩
    isplitl [HA]
    · iexact HA
    · isplitl []
      · iexact HS
      · isplitl []
        · iexact HS
        · iexact HR

/-- Weaken `satisfiedBy` in the resource via an entailment. -/
theorem SpecMap.satisfiedBy_weaken {A R : iProp}
    (h : SpecMap.satisfiedBy Θ S γ ⊢ SpecMap.satisfiedBy Θ' S' γ') :
    A ∗ (SpecMap.satisfiedBy Θ S γ ∗ R) ⊢ A ∗ (SpecMap.satisfiedBy Θ' S' γ' ∗ R) :=
  sep_mono_r (sep_mono_l h)

/-! ### Correctness -/

/-! #### Correctness Statements -/

def correctExpr (e : Expr) : Prop :=
  ∀ (Θ : TinyML.TypeEnv) (R : iProp) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) (st : TransState) (ρ : VerifM.Env) (γ : Runtime.Subst)
  (Ψ : Term .value → TransState → VerifM.Env → Prop) (Φ : Runtime.Val → iProp),
    VerifM.eval (compile Θ S B Γ e) st ρ Ψ →
    B.agreeOnLinked ρ.env γ →
    B.wf st.decls →
    B.typedSubst Θ Γ γ →
    S.wfIn Signature.empty →
    (∀ v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls → Term.eval ρ'.env se = v →
      TinyML.ValHasType Θ v e.ty → st'.sl ρ' ∗ R ⊢ Φ v) →
    st.sl ρ ∗ (S.satisfiedBy Θ γ ∗ R) ⊢ wp (e.runtime.subst γ) Φ

def correctBranch (branch : Binder × Expr) : Prop :=
  ∀ (Θ : TinyML.TypeEnv) (R : iProp) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (sc : Term .value) (n i : Nat) (ty_i : TinyML.Typ)
    (st : TransState) (ρ : VerifM.Env) (γ : Runtime.Subst)
    (Ψ : Term .value → TransState → VerifM.Env → Prop)
    (Φ : Runtime.Val → iProp),
    VerifM.eval (compileBranch Θ S B Γ sc n i ty_i branch) st ρ Ψ →
    B.agreeOnLinked ρ.env γ →
    B.wf st.decls →
    B.typedSubst Θ Γ γ →
    S.wfIn Signature.empty →
    sc.wfIn st.decls →
    (∀ v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls →
      se.eval ρ'.env = v → TinyML.ValHasType Θ v branch.2.ty → st'.sl ρ' ∗ (S.satisfiedBy Θ γ ∗ R) ⊢ Φ v) →
    ∀ payload, sc.eval ρ.env = Runtime.Val.inj i n payload →
      TinyML.ValHasType Θ payload ty_i →
      st.sl ρ ∗ (S.satisfiedBy Θ γ ∗ R) ⊢ wp (.app ((Runtime.Expr.fix .none [branch.1.runtime] branch.2.runtime).subst γ) [.val payload]) Φ

def correctBranches (branches : List (Binder × Expr)) : Prop :=
  ∀ (Θ : TinyML.TypeEnv) (R : iProp) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (sc : Term .value) (n : Nat) (ts : List TinyML.Typ) (idx : Nat)
    (st : TransState) (ρ : VerifM.Env) (γ : Runtime.Subst)
    (Ψ : Term .value → TransState → VerifM.Env → Prop)
    (Φ : Runtime.Val → iProp),
    B.agreeOnLinked ρ.env γ →
    B.wf st.decls →
    B.typedSubst Θ Γ γ →
    S.wfIn Signature.empty →
    sc.wfIn st.decls →
    (∀ (j : Nat) (hj : j < branches.length) v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls →
      se.eval ρ'.env = v → TinyML.ValHasType Θ v (branches[j]).2.ty → st'.sl ρ' ∗ (S.satisfiedBy Θ γ ∗ R) ⊢ Φ v) →
    ∀ (j : Nat) (hj : j < branches.length),
      VerifM.eval (compileBranch Θ S B Γ sc n (idx + j) (ts[idx + j]?.getD .value) branches[j]) st ρ Ψ →
      ∀ payload, sc.eval ρ.env = Runtime.Val.inj (idx + j) n payload →
        TinyML.ValHasType Θ payload (ts[idx + j]?.getD .value) →
        st.sl ρ ∗ (S.satisfiedBy Θ γ ∗ R) ⊢ wp (.app ((Runtime.Expr.fix .none [(branches[j]).1.runtime] (branches[j]).2.runtime).subst γ) [.val payload]) Φ

def correctExprs (es : List Expr) : Prop :=
  ∀ (Θ : TinyML.TypeEnv) (R : iProp) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (st : TransState) (ρ : VerifM.Env) (γ : Runtime.Subst)
    (Ψ : List (Term .value) → TransState → VerifM.Env → Prop)
    (Φ : List Runtime.Val → iProp),
    VerifM.eval (compileExprs Θ S B Γ es) st ρ Ψ →
    B.agreeOnLinked ρ.env γ →
    B.wf st.decls →
    B.typedSubst Θ Γ γ →
    S.wfIn Signature.empty →
    (∀ vs ρ' st' terms, Ψ terms st' ρ' →
      (∀ t ∈ terms, t.wfIn st'.decls) →
      Terms.Eval ρ'.env terms vs →
      TinyML.ValsHaveTypes Θ vs (es.map Expr.ty) → st'.sl ρ' ∗ (S.satisfiedBy Θ γ ∗ R) ⊢ Φ vs) →
    st.sl ρ ∗ (S.satisfiedBy Θ γ ∗ R) ⊢ wps (es.map (fun e => e.runtime.subst γ)) Φ

/-! #### Correctness Compatibility Lemmas -/

theorem compileConst_correct (c : TinyML.Const) :
    correctExpr (.const c) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval _hagree _hbwf _hts _hSwf hpost
  cases c with
  | int n =>
    simp only [compile] at heval
    simp only [Expr.runtime, TinyML.Const.runtime, Runtime.Expr.subst_val]
    obtain heval := VerifM.eval_ret heval
    simp only [Expr.ty, Const.ty] at hpost
    exact SpatialContext.wp_val <| (sep_mono_r sep_elim_r).trans <| hpost (.int n) ρ st _ heval
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.denote])
      (.int n)
  | bool b =>
    simp only [compile] at heval
    simp only [Expr.runtime, TinyML.Const.runtime, Runtime.Expr.subst_val]
    obtain heval := VerifM.eval_ret heval
    simp only [Expr.ty, Const.ty] at hpost
    exact SpatialContext.wp_val <| (sep_mono_r sep_elim_r).trans <| hpost (.bool b) ρ st _ heval
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.denote])
      (.bool b)
  | unit =>
    simp only [compile] at heval
    simp only [Expr.runtime, TinyML.Const.runtime, Runtime.Expr.subst_val]
    obtain heval := VerifM.eval_ret heval
    simp only [Expr.ty, Const.ty] at hpost
    exact SpatialContext.wp_val <| (sep_mono_r sep_elim_r).trans <| hpost .unit ρ st _ heval
      (by simp [Term.wfIn, Const.wfIn])
      (by simp [Term.eval])
      .unit

theorem compileVar_correct (x : String) (vty : TinyML.Typ) :
    correctExpr (.var x vty) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts _hSwf hpost
  simp only [compile] at heval
  obtain ⟨x', hbind, heval⟩ := VerifM.eval_bind_expectSome heval
  by_cases hcheck : (Γ x |>.getD .value) = vty
  · obtain ⟨_, hcont⟩ := VerifM.eval_bind_expectEq heval
    unfold Expr.runtime; simp only [Runtime.Expr.subst]
    obtain ⟨hsort, hγ⟩ := hagree x x' hbind
    rw [hγ]; simp
    have hmem : (x, x') ∈ B := by
      obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hbind
      rw [heq]; simp
    have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
    obtain heval := VerifM.eval_ret hcont
    have hwfv : (Term.const (.uninterpreted x'.name .value)).wfIn st.decls := by
      simp only [Term.wfIn, Const.wfIn]
      have h := hbwf _ hmem
      cases x' with
      | mk n s =>
        simp only at hsort
        subst hsort
        refine ⟨h, ?_, ?_⟩
        · intro τ' hvar
          exact Signature.wf_no_var_of_const hwfst h hvar
        · intro τ' hc'
          exact Signature.wf_unique_const hwfst h hc'
    simp only [Expr.ty] at hpost
    have htyping : TinyML.ValHasType Θ (ρ.env.consts .value x'.name) vty := by
      rw [← hcheck]
      cases hΓ : Γ x with
      | none => exact .any
      | some t =>
        obtain ⟨w, hw, hwt⟩ := hts x x' t hbind hΓ
        rw [hγ] at hw
        exact (Option.some.inj hw) ▸ hwt
    exact SpatialContext.wp_val <| (sep_mono_r sep_elim_r).trans <|
      hpost _ ρ st _ heval hwfv (by simp [Term.eval, Const.denote]) htyping
  · exact False.elim (hcheck (VerifM.eval_bind_expectEq heval).1)

theorem compileInj_correct (tag arity : Nat) (payload : Expr)
    (ihPayload : correctExpr payload) :
    correctExpr (.inj tag arity payload) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  unfold Expr.runtime; simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  by_cases htag : tag ≥ arity
  · simp [htag] at heval; exact (VerifM.eval_fatal heval).elim
  · push_neg at htag
    simp [show ¬(tag ≥ arity) from Nat.not_le.mpr htag] at heval
    have heval_p : (compile Θ S B Γ payload).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine SpatialContext.wp_bind_inj <| ihPayload Θ R S B Γ st ρ γ _ _
      (VerifM.eval.decls_grow ρ heval_p) hagree hbwf hts hSwf ?_
    intro v_p ρ_p st_p se_p hΨ_p hse_wf_p heval_se_p htype_p
    obtain ⟨hdecls_p, hagreeOn_p, hΨ_p⟩ := hΨ_p
    obtain hΨ_p := VerifM.eval_ret hΨ_p
    simp only [Expr.ty] at hpost
    refine SpatialContext.wp_inj <| hpost (.inj tag arity v_p) ρ_p st_p _ hΨ_p
        (by simp only [Term.wfIn]; exact ⟨trivial, hse_wf_p⟩)
        (by simp [Term.eval, UnOp.eval, heval_se_p])
        (by
          let ts := (List.replicate arity TinyML.Typ.empty).set tag payload.ty
          have hlen_ts : ts.length = arity := by simp [ts]
          have : TinyML.ValHasType Θ (.inj tag ts.length v_p) (.sum ts) :=
            .inj (ts := ts) (by simp [ts, htag]) htype_p
          rwa [hlen_ts] at this)

theorem compileCast_correct (e : Expr) (ty : TinyML.Typ)
    (ih : correctExpr e) :
    correctExpr (.cast e ty) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  simp only [Expr.ty] at hpost
  simp only [compile] at heval
  have heval_e : (compile Θ S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  simp [Expr.runtime]
  refine ih Θ R S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hts hSwf ?_
  intro v ρ' st' se hΨ hse_wf heval_se htype_v
  obtain ⟨_, _, hΨ⟩ := hΨ
  cases hsub : TinyML.Typ.sub Θ e.ty ty
  · simp [hsub] at hΨ
    exact (VerifM.eval_fatal hΨ).elim
  · simp [hsub] at hΨ
    obtain hΨ := VerifM.eval_ret hΨ
    have hsub' : TinyML.Typ.Sub Θ e.ty ty := TinyML.Typ.sub_sound hsub
    exact hpost v ρ' st' se hΨ hse_wf heval_se (TinyML.ValHasType_sub htype_v hsub')

theorem compileAssert_correct (e : Expr)
    (ih : correctExpr e) :
    correctExpr (.assert e) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  unfold Expr.runtime; simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  have heval_e : (compile Θ S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_assert <| ih Θ R S B Γ st ρ γ _ _
    (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hts hSwf ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se _
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
  exact SpatialContext.wp_assert <| hpost .unit ρ_e st₁ (Term.const .unit) hΨ_pure
    trivial
    (by simp [Term.eval])
    .unit

theorem compileFix_correct (self : Binder) (args : List Binder) (retTy : TinyML.Typ) (body : Expr) :
    correctExpr (.fix self args retTy body) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval _hagree _hbwf _hts _hSwf _hpost
  simp only [compile] at heval
  exact (VerifM.eval_fatal heval).elim

theorem compileRef_correct (e : Expr)
    (ih : correctExpr e) :
    correctExpr (.ref e) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  unfold Expr.runtime; simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  simp only [Expr.ty] at hpost
  have heval_e : (compile Θ S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_ref <| ih Θ R S B Γ st ρ γ _ _
    (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hts hSwf ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se _htype_e
  obtain ⟨_hdecls_e, _hagreeOn_e, hΨ_e⟩ := hΨ_e
  have hwf_st₁ := VerifM.eval.wf hΨ_e
  set c : FOL.Const := st₁.freshConst none .value
  have hfresh : c.name ∉ st₁.decls.allNames :=
    fresh_not_mem _ _ (addNumbers_injective _)
  have hwf_addConst : TransState.wf { st₁ with decls := st₁.decls.addConst c } :=
    TransState.freshConst.wf _ hwf_st₁
  refine SpatialContext.wp_ref (ctx := st₁.owns) (Δ := st₁.decls) (vt := se)
    (name := c.name)
    (newctx := .pointsTo (.const (.uninterpreted c.name .value)) se :: st₁.owns)
    hwf_st₁.ownsWf hse_wf heval_se hfresh rfl ?_
  intro loc
  have hdecl_eval := VerifM.eval_bind _ _ _ _ hΨ_e
  have hdecl := VerifM.eval_decl hdecl_eval (.loc loc)
  have hassume_eval := VerifM.eval_bind _ _ _ _ hdecl
  set ρ_e' : VerifM.Env := ρ_e.updateConst .value c.name (.loc loc)
  set st₂ : TransState := { st₁ with decls := st₁.decls.addConst c }
  have hc_wf : (Term.const (.uninterpreted c.name .value)).wfIn st₂.decls := by
    simp only [Term.wfIn, Const.wfIn]
    refine ⟨List.Mem.head _, ?_, ?_⟩
    · intro τ' hvar
      exact Signature.wf_no_var_of_const hwf_addConst.namesDisjoint
        (List.Mem.head _) hvar
    · intro τ' hc'
      exact Signature.wf_unique_const hwf_addConst.namesDisjoint (List.Mem.head _) hc'
  have hse_wf_st₂ : se.wfIn st₂.decls :=
    Term.wfIn_mono se hse_wf (Signature.Subset.subset_addConst _ _) hwf_addConst.namesDisjoint
  have hatom_wf : SpatialAtom.wfIn
      (.pointsTo (.const (.uninterpreted c.name .value)) se) st₂.decls :=
    ⟨hc_wf, hse_wf_st₂⟩
  have hassume_res := VerifM.eval_assumeSpatial hassume_eval hatom_wf
  have hret := VerifM.eval_ret hassume_res
  have hval_eval : Term.eval ρ_e'.env (Term.const (.uninterpreted c.name .value)) = .loc loc := by
    simp [Term.eval, Const.denote, ρ_e', VerifM.Env.updateConst, Env.updateConst]
  have hty : TinyML.ValHasType Θ (Runtime.Val.loc loc) (TinyML.Typ.ref e.ty) := by
    exact TinyML.ValHasType.ref loc e.ty
  exact hpost (.loc loc) ρ_e' _ _ hret hc_wf hval_eval hty

theorem compileDeref_correct (e : Expr) (ty : TinyML.Typ)
    (ih : correctExpr e) :
    correctExpr (.deref e ty) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  unfold Expr.runtime; simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  simp only [Expr.ty] at hpost
  obtain ⟨_hannot, heval⟩ := VerifM.eval_bind_expectEq heval
  cases hty : ty with
  | int =>
    simp [hty] at heval hpost
    have heval_e : (compile Θ S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine SpatialContext.wp_bind_deref <| ih Θ R S B Γ st ρ γ _ _
      (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hts hSwf ?_
    intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se _htype_e
    obtain ⟨_hdecls_e, _hagreeOn_e, hΨ_e⟩ := hΨ_e
    have hres_bind := VerifM.eval_bind _ _ _ _ hΨ_e
    refine VerifM.eval_resolve (pred := .own se) (R := R)
      (Φ := wp (.deref (.val v_e)) Φ) hres_bind hse_wf ?_ ?_
    · intro st' hQ _
      exact (VerifM.eval_failed hQ).elim
    · intro v st' hQ hdecls hvwf
      have hassert_bind := VerifM.eval_bind _ _ _ _ hQ
      have hse_wf_st' : se.wfIn st'.decls := hdecls ▸ hse_wf
      have hv_wf_st' : v.wfIn st'.decls := hdecls ▸ hvwf
      have hassert_wf : (Formula.unpred .isInt v).wfIn st'.decls := hv_wf_st'
      have ⟨hv_int, hQ⟩ := VerifM.eval_assert hassert_bind hassert_wf
      have hassume_bind := VerifM.eval_bind _ _ _ _ hQ
      have hatom_wf : SpatialAtom.wfIn (.pointsTo se v) st'.decls :=
        ⟨hse_wf_st', hv_wf_st'⟩
      have hassume_res := VerifM.eval_assumeSpatial hassume_bind hatom_wf
      have hret := VerifM.eval_ret hassume_res
      have hv_wf_final : v.wfIn (TransState.addItem st' (.spatial (.pointsTo se v))).decls := by
        simpa [TransState.addItem] using hv_wf_st'
      have htype : TinyML.ValHasType Θ (v.eval ρ_e.env) .int := by
        cases hv : v.eval ρ_e.env with
        | int n => exact TinyML.ValHasType.int n
        | bool _ | unit | inj _ _ _ | loc _ | fix _ _ _ | tuple _ =>
            simp [Formula.eval, hv] at hv_int
      let st'' := TransState.addItem st' (.spatial (.pointsTo se v))
      have hgoal : st''.sl ρ_e ∗ R ⊢ Φ (v.eval ρ_e.env) :=
        hpost (v.eval ρ_e.env) ρ_e st'' _ hret hv_wf_final rfl htype
      simp only [Atom.eval]
      istart
      iintro H
      icases H with ⟨Hex, Hrest, HR⟩
      icases Hex with ⟨%loc, Hpt'⟩
      icases Hpt' with ⟨%Hloc, Hpt⟩
      have hv_e : v_e = .loc loc := heval_se.symm.trans Hloc
      subst hv_e
      have hptIntro : loc ↦ v.eval ρ_e.env ⊢ SpatialAtom.interp ρ_e.env (.pointsTo se v) := by
        simpa [Hloc] using
          (SpatialAtom.interp_pointsTo (ρ := ρ_e.env) (lt := se) (vt := v) (loc := loc) Hloc).2
      have hctx : (loc ↦ v.eval ρ_e.env) ∗ SpatialContext.interp ρ_e.env st'.owns ∗ R ⊢ Φ (v.eval ρ_e.env) := by
        have hcons : (loc ↦ v.eval ρ_e.env) ∗ SpatialContext.interp ρ_e.env st'.owns ⊢ st''.sl ρ_e := by
          simpa [st'', TransState.addItem, SpatialContext.interp] using (sep_mono_l hptIntro)
        exact sep_assoc.2.trans ((sep_mono_l hcons).trans hgoal)
      iapply (wp.deref (l := loc) (v := v.eval ρ_e.env))
      isplitl [Hpt]
      · iexact Hpt
      · iintro Hpt
        iapply hctx
        isplitl [Hpt]
        · iexact Hpt
        · isplitl [Hrest]
          · simp [TransState.sl]
          · iexact HR
  | bool | unit | arrow _ _ | ref _ | sum _ | empty | value | tuple _ | tvar _ | named _ _ =>
    simp [hty] at heval
    exact (VerifM.eval_fatal heval).elim

theorem compileStore_correct (loc val : Expr)
    (ihVal : correctExpr val) (ihLoc : correctExpr loc) :
    correctExpr (.store loc val) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  unfold Expr.runtime; simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  simp only [Expr.ty] at hpost
  obtain ⟨_hannot, heval⟩ := VerifM.eval_bind_expectEq heval
  have heval_v : (compile Θ S B Γ val).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_store <| (SpecMap.satisfiedBy_dup.trans <|
    ihVal Θ (S.satisfiedBy Θ γ ∗ R) S B Γ st ρ γ _ _
      (VerifM.eval.decls_grow ρ heval_v) hagree hbwf hts hSwf ?_)
  intro v_v ρ_v st₁ sv hΨ_v hsv_wf heval_sv htyv
  obtain ⟨hdecls_v, hagreeOn_v, hΨ_v⟩ := hΨ_v
  have hagree_v : B.agreeOnLinked ρ_v.env γ :=
    Bindings.agreeOnLinked_env_agree hagree hagreeOn_v hbwf
  have hbwf_v : B.wf st₁.decls := fun p hp => hdecls_v.consts _ (hbwf p hp)
  have heval_l : (compile Θ S B Γ loc).eval st₁ ρ_v _ := VerifM.eval_bind _ _ _ _ hΨ_v
  refine ihLoc Θ R S B Γ st₁ ρ_v γ _ _
    (VerifM.eval.decls_grow ρ_v heval_l) hagree_v hbwf_v hts hSwf ?_
  intro v_l ρ_l st₂ sl hΨ_l hsl_wf heval_sl htyl
  obtain ⟨hdecls_l, hagreeOn_l, hΨ_l⟩ := hΨ_l
  have hsv_ρ_l : sv.eval ρ_l.env = v_v := by
    rw [Term.eval_env_agree hsv_wf (Env.agreeOn_symm hagreeOn_l)]
    exact heval_sv
  have hres_bind := VerifM.eval_bind _ _ _ _ hΨ_l
  refine VerifM.eval_resolve (pred := .own sl) (R := R)
    (Φ := wp (.store (.val v_l) (.val v_v)) Φ) hres_bind hsl_wf ?_ ?_
  · intro st' hQ _
    exact (VerifM.eval_failed hQ).elim
  · intro old st' hQ hdecls hold_wf
    have hassume_bind := VerifM.eval_bind _ _ _ _ hQ
    have hsl_wf_st' : sl.wfIn st'.decls := hdecls ▸ hsl_wf
    have hsv_wf_st₂ : sv.wfIn st₂.decls :=
      Term.wfIn_mono sv hsv_wf hdecls_l (VerifM.eval.wf hΨ_l).namesDisjoint
    have hsv_wf_st' : sv.wfIn st'.decls := hdecls ▸ hsv_wf_st₂
    have hatom_wf : SpatialAtom.wfIn (.pointsTo sl sv) st'.decls :=
      ⟨hsl_wf_st', hsv_wf_st'⟩
    have hassume_res := VerifM.eval_assumeSpatial hassume_bind hatom_wf
    have hret := VerifM.eval_ret hassume_res
    have hunit_wf : (Term.const .unit).wfIn
        (TransState.addItem st' (.spatial (.pointsTo sl sv))).decls := by
      simp [Term.wfIn, Const.wfIn]
    let st'' := TransState.addItem st' (.spatial (.pointsTo sl sv))
    have hgoal : st''.sl ρ_l ∗ R ⊢ Φ .unit :=
      hpost .unit ρ_l st'' _ hret hunit_wf (by simp [Term.eval]) (.unit)
    simp only [Atom.eval]
    istart
    iintro H
    icases H with ⟨Hex, Hrest, HR⟩
    icases Hex with ⟨%loc, Hold'⟩
    icases Hold' with ⟨%Hloc, Hold⟩
    have hv_l : v_l = .loc loc := heval_sl.symm.trans Hloc
    subst hv_l
    have hnewIntro : loc ↦ v_v ⊢ SpatialAtom.interp ρ_l.env (.pointsTo sl sv) := by
      simpa [Hloc, hsv_ρ_l] using
        (SpatialAtom.interp_pointsTo (ρ := ρ_l.env) (lt := sl) (vt := sv) (loc := loc) Hloc).2
    have hctx : (loc ↦ v_v) ∗ SpatialContext.interp ρ_l.env st'.owns ∗ R ⊢ Φ .unit := by
      have hcons : (loc ↦ v_v) ∗ SpatialContext.interp ρ_l.env st'.owns ⊢ st''.sl ρ_l := by
        simpa [st'', TransState.addItem, SpatialContext.interp] using (sep_mono_l hnewIntro)
      exact sep_assoc.2.trans ((sep_mono_l hcons).trans hgoal)
    iapply (wp.store (l := loc) (old := old.eval ρ_l.env) (v := v_v))
    isplitl [Hold]
    · iexact Hold
    · iintro Hnew
      iapply hctx
      isplitl [Hnew]
      · iexact Hnew
      · isplitl [Hrest]
        · simp [TransState.sl]
        · iexact HR

theorem compileUnop_correct (op : TinyML.UnOp) (e : Expr) (uty : TinyML.Typ)
    (ih : correctExpr e) :
    correctExpr (.unop op e uty) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  unfold Expr.runtime; simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  have heval_e : (compile Θ S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_unop <| ih Θ R S B Γ st ρ γ _ _
    (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hts hSwf ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se htype_e
  obtain ⟨_, _, hΨ_e⟩ := hΨ_e
  obtain ⟨ty, htypeOf, hΨ_e⟩ := VerifM.eval_bind_expectSome hΨ_e
  obtain ⟨hty_eq, hΨ_e⟩ := VerifM.eval_bind_expectEq hΨ_e
  obtain ⟨t, hcompUnop, hΨ_e⟩ := VerifM.eval_bind_expectSome hΨ_e
  obtain hΨ_e := VerifM.eval_ret hΨ_e
  obtain ⟨w, heval_op, hwt⟩ := evalUnOp_typed htypeOf htype_e
  have ht_eval : t.eval ρ_e.env = w :=
    compileUnop_eval heval_se heval_op hcompUnop
  simp only [Expr.ty] at hpost
  exact SpatialContext.wp_unop
    (hpost w ρ_e st₁ t hΨ_e
      (compileUnop_wfIn hse_wf hcompUnop) ht_eval (hty_eq ▸ hwt))
    heval_op

theorem compileBinop_correct (op : TinyML.BinOp) (l r : Expr) (bty : TinyML.Typ)
    (ihR : correctExpr r) (ihL : correctExpr l) :
    correctExpr (.binop op l r bty) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  unfold Expr.runtime; simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  have heval_r : (compile Θ S B Γ r).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_binop <| (SpecMap.satisfiedBy_dup).trans <|
    ihR Θ (S.satisfiedBy Θ γ ∗ R) S B Γ st ρ γ _ _
    (VerifM.eval.decls_grow ρ heval_r) hagree hbwf hts hSwf ?_
  intro vr ρ_r st₁ sr hΨ_r hsr_wf heval_sr htyr
  obtain ⟨hdecls_r, hagreeOn_r, hΨ_r⟩ := hΨ_r
  have hagree_r : B.agreeOnLinked ρ_r.env γ :=
    Bindings.agreeOnLinked_env_agree hagree hagreeOn_r hbwf
  have hbwf_r : B.wf st₁.decls := fun p hp => hdecls_r.consts _ (hbwf p hp)
  have heval_l : (compile Θ S B Γ l).eval st₁ ρ_r _ := VerifM.eval_bind _ _ _ _ hΨ_r
  refine ihL Θ R S B Γ st₁ ρ_r γ _ _
    (VerifM.eval.decls_grow ρ_r heval_l) hagree_r hbwf_r hts hSwf ?_
  intro vl ρ_l st₂ sl hΨ_l hsl_wf heval_sl htyl
  obtain ⟨hdecls_l, hagreeOn_l, hΨ_l⟩ := hΨ_l
  obtain ⟨ty, htypeOf, hΨ_l⟩ := VerifM.eval_bind_expectSome hΨ_l
  obtain ⟨hty_eq, hΨ_l'⟩ := VerifM.eval_bind_expectEq hΨ_l
  simp only [Expr.ty] at hpost
  have hsr_ρ_l : sr.eval ρ_l.env = vr := by
    rw [Term.eval_env_agree hsr_wf (Env.agreeOn_symm hagreeOn_l)]; exact heval_sr
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
      have hlty : l.ty = .int := by
        revert htypeOf; cases l.ty <;> simp [TinyML.BinOp.typeOf]
      have hrty : r.ty = .int := by
        revert htypeOf; cases r.ty <;> simp [TinyML.BinOp.typeOf, hlty]
      rw [hlty] at htyl; rw [hrty] at htyr
      cases htyl with
      | int a =>
        cases htyr with
        | int b =>
          have hassert_wf : (Formula.not (.eq .int (.unop .toInt sr) (.const (.i 0)))).wfIn st₂.decls := by
            simpa [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn] using
              (Term.wfIn_mono sr hsr_wf hdecls_l (VerifM.eval.wf hΨ_div).namesDisjoint)
          have heval_assert := VerifM.eval_bind _ _ _ _ hΨ_div
          have ⟨hne_zero, hΨ_post⟩ := VerifM.eval_assert heval_assert hassert_wf
          simp [Formula.eval, Term.eval, Const.denote] at hne_zero
          rw [hsr_ρ_l] at hne_zero
          simp at hne_zero
          obtain hΨ_post := VerifM.eval_ret hΨ_post
          have hty_int : ty = .int := by
            rw [hlty, hrty] at htypeOf
            simpa [TinyML.BinOp.typeOf] using htypeOf.symm
          have hbty : bty = .int := hty_eq.symm.trans hty_int
          have hwf_sr_l : sr.wfIn st₂.decls :=
            Term.wfIn_mono sr hsr_wf hdecls_l (VerifM.eval.wf hΨ_div).namesDisjoint
          have hwf_bin : (Term.unop .ofInt (Term.binop BinOp.div (Term.unop .toInt sl) (Term.unop .toInt sr))).wfIn st₂.decls := by
            simpa [Term.wfIn, BinOp.wfIn, UnOp.wfIn] using And.intro hsl_wf hwf_sr_l
          have hΨ_post' : Ψ (Term.unop .ofInt (Term.binop BinOp.div (Term.unop .toInt sl) (Term.unop .toInt sr))) st₂ ρ_l := by
            simpa using hΨ_post
          exact SpatialContext.wp_binop
            (hpost (.int (a / b)) ρ_l st₂ _ hΨ_post' hwf_bin
              (by simp [Term.eval, UnOp.eval, BinOp.eval, heval_sl, hsr_ρ_l])
              (hbty ▸ .int _))
            (by simp [TinyML.evalBinOp, hne_zero])
    · subst hmod
      have hlty : l.ty = .int := by
        revert htypeOf; cases l.ty <;> simp [TinyML.BinOp.typeOf]
      have hrty : r.ty = .int := by
        revert htypeOf; cases r.ty <;> simp [TinyML.BinOp.typeOf, hlty]
      rw [hlty] at htyl; rw [hrty] at htyr
      cases htyl with
      | int a =>
        cases htyr with
        | int b =>
          have hassert_wf : (Formula.not (.eq .int (.unop .toInt sr) (.const (.i 0)))).wfIn st₂.decls := by
            simpa [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn] using
              (Term.wfIn_mono sr hsr_wf hdecls_l (VerifM.eval.wf hΨ_div).namesDisjoint)
          have heval_assert := VerifM.eval_bind _ _ _ _ hΨ_div
          have ⟨hne_zero, hΨ_post⟩ := VerifM.eval_assert heval_assert hassert_wf
          simp [Formula.eval, Term.eval, Const.denote] at hne_zero
          rw [hsr_ρ_l] at hne_zero
          simp at hne_zero
          obtain hΨ_post := VerifM.eval_ret hΨ_post
          have hty_int : ty = .int := by
            rw [hlty, hrty] at htypeOf
            simpa [TinyML.BinOp.typeOf] using htypeOf.symm
          have hbty : bty = .int := hty_eq.symm.trans hty_int
          have hwf_sr_l : sr.wfIn st₂.decls :=
            Term.wfIn_mono sr hsr_wf hdecls_l (VerifM.eval.wf hΨ_div).namesDisjoint
          have hwf_bin : (Term.unop .ofInt (Term.binop BinOp.mod (Term.unop .toInt sl) (Term.unop .toInt sr))).wfIn st₂.decls := by
            simpa [Term.wfIn, BinOp.wfIn, UnOp.wfIn] using And.intro hsl_wf hwf_sr_l
          have hΨ_post' : Ψ (Term.unop .ofInt (Term.binop BinOp.mod (Term.unop .toInt sl) (Term.unop .toInt sr))) st₂ ρ_l := by
            simpa using hΨ_post
          exact SpatialContext.wp_binop
            (hpost (.int (a % b)) ρ_l st₂ _ hΨ_post' hwf_bin
              (by simp [Term.eval, UnOp.eval, BinOp.eval, heval_sl, hsr_ρ_l])
              (hbty ▸ .int _))
            (by simp [TinyML.evalBinOp, hne_zero])
  · have hndivmod : ¬(op = TinyML.BinOp.div ∨ op = TinyML.BinOp.mod) := hdivmod
    have hΨ_ndiv :
          (do
            let t ← VerifM.expectSome
              s!"unsupported binary operator: {repr op}"
              (compileOp op sl sr)
            pure t).eval st₂ ρ_l Ψ := by
      simpa [hndivmod] using hΨ_l'
    obtain ⟨t, hcompOp, hΨ_ndiv⟩ := VerifM.eval_bind_expectSome hΨ_ndiv
    have hwfst₂ : st₂.decls.wf := (VerifM.eval.wf hΨ_ndiv).namesDisjoint
    obtain hΨ_ndiv := VerifM.eval_ret hΨ_ndiv
    have hdiv : op ≠ .div := fun h => hndivmod (Or.inl h)
    have hmod : op ≠ .mod := fun h => hndivmod (Or.inr h)
    obtain ⟨w, heval_op, hwt⟩ := evalBinOp_typed hdiv hmod htypeOf htyl htyr
    have hwf_sr_l : sr.wfIn st₂.decls :=
      Term.wfIn_mono sr hsr_wf hdecls_l hwfst₂
    have ht_eval : t.eval ρ_l.env = w := compileOp_eval heval_sl hsr_ρ_l heval_op hcompOp
    exact SpatialContext.wp_binop
      (hpost w ρ_l st₂ t hΨ_ndiv
        (compileOp_wfIn hsl_wf hwf_sr_l hcompOp) ht_eval (hty_eq ▸ hwt))
      heval_op

theorem compileLetIn_correct (b : Binder) (e body : Expr)
    (ihE : correctExpr e) (ihBody : correctExpr body) :
    correctExpr (.letIn b e body) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  simp only [compile] at heval
  simp only [Expr.ty] at hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.letIn_subst]
  have heval_e_outer : (compile Θ S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine (SpecMap.satisfiedBy_dup.trans <| ihE Θ (S.satisfiedBy Θ γ ∗ R) S B Γ st ρ γ _ _
    (VerifM.eval.decls_grow ρ heval_e_outer) hagree hbwf hts hSwf ?_).trans wp.letIn
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_e htyping_e
  obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
  have hagree_e := Bindings.agreeOnLinked_env_agree hagree hagreeOn_e hbwf
  have hbwf_e : B.wf st₁.decls := fun p hp => hdecls_e.consts _ (hbwf p hp)
  obtain ⟨_, hΨ_e⟩ := VerifM.eval_bind_expectEq hΨ_e
  cases hname : b.name with
  | none =>
    simp [hname] at hΨ_e
    have hbody := ihBody Θ R S B Γ st₁ ρ_e γ _ _
      (VerifM.eval.decls_grow ρ_e hΨ_e) hagree_e hbwf_e hts hSwf
      (fun v ρ' st' se hΨ hs hw ht =>
        let ⟨_, _, hΨ'⟩ := hΨ
        hpost v ρ' st' se hΨ' hs hw ht)
    have hsubst := Runtime.Expr.subst_remove'_update' body.runtime γ Runtime.Binder.none v_e
    have hbody' : st₁.sl ρ_e ∗ (S.satisfiedBy Θ γ ∗ R) ⊢ wp
          (Runtime.Expr.subst
            (Runtime.Subst.update' Runtime.Binder.none v_e Runtime.Subst.id)
            (Runtime.Expr.subst (γ.remove' Runtime.Binder.none) body.runtime))
          Φ :=
      hsubst.symm ▸ hbody
    rw [Binder.runtime_of_name_none hname]
    simpa [Runtime.Subst.update'] using hbody'
  | some x =>
    simp [hname] at hΨ_e
    set base := x
    set x' := fresh (addNumbers base) st₁.decls.allNames
    set v : FOL.Const := ⟨x', .value⟩
    have _hvty : v.sort = .value := rfl
    have hfresh : v.name ∉ st₁.decls.allNames :=
      fresh_not_mem _ _ (addNumbers_injective _)
    set st₂ : TransState :=
      { decls := st₁.decls.addConst v,
        asserts := (Formula.eq .value (.const (.uninterpreted v.name .value)) se) :: st₁.asserts,
        owns := st₁.owns }
    set ρ_body := ρ_e.updateConst .value v.name v_e
    set γ_body : Runtime.Subst := Runtime.Subst.update γ x v_e
    suffices st₂.sl ρ_body ∗ (SpecMap.satisfiedBy Θ (Finmap.erase x S) γ_body ∗ R) ⊢ wp (body.runtime.subst γ_body) Φ by
      have hsubst := Runtime.Expr.subst_remove'_update' body.runtime γ (.named x) v_e
      have hbody' : st₂.sl ρ_body ∗ (SpecMap.satisfiedBy Θ (Finmap.erase x S) γ_body ∗ R) ⊢ wp
            (Runtime.Expr.subst
              (Runtime.Subst.update' (.named x) v_e Runtime.Subst.id)
              (Runtime.Expr.subst (γ.remove' (.named x)) body.runtime))
            Φ :=
        hsubst.symm ▸ this
      have hinterp_eq : SpatialContext.interp ρ_e.env st₁.owns ⊢ SpatialContext.interp ρ_body.env st₁.owns :=
        (SpatialContext.interp_env_agree (VerifM.eval.wf hΨ_e).ownsWf
          (agreeOn_update_fresh_const hfresh)).1
      rw [Binder.runtime_of_name_some hname]
      have hsat :
          st₂.sl ρ_body ∗ (S.satisfiedBy Θ γ ∗ R) ⊢
            st₂.sl ρ_body ∗ (SpecMap.satisfiedBy Θ (Finmap.erase x S) γ_body ∗ R) := by
        exact SpecMap.satisfiedBy_weaken SpecMap.satisfiedBy_erase
      exact (sep_mono_l hinterp_eq).trans <|
        hsat.trans <|
        by simpa [st₂, γ_body, base, Runtime.Subst.update', Runtime.Subst.update, Runtime.Subst.id]
          using hbody'
    have hagreeOn_body_e : Env.agreeOn st₁.decls ρ_e.env ρ_body.env :=
      agreeOn_update_fresh_const hfresh
    have hΨ_body : (compile Θ (Finmap.erase x S) ((x, v) :: B) (Γ.extend x e.ty) body).eval st₂ ρ_body Ψ := by
      have hdecl_eval := VerifM.eval_bind _ _ _ _ hΨ_e
      have hdecl := VerifM.eval_decl hdecl_eval
      have h := hdecl v_e
      obtain h := VerifM.eval_bind _ _ _ _ h
      obtain h := VerifM.eval_assumePure h
      apply h
      · simp only [Formula.wfIn, Term.wfIn, Const.wfIn]
        refine ⟨?_, Term.wfIn_mono se hse_wf (Signature.Subset.subset_addConst _ _)
          (TransState.freshConst.wf _ (VerifM.eval.wf hdecl_eval)).namesDisjoint⟩
        refine ⟨List.mem_cons_self .., ?_, ?_⟩
        · intro τ' hvar
          exact Signature.wf_no_var_of_const
            (TransState.freshConst.wf _ (VerifM.eval.wf hdecl_eval)).namesDisjoint
            (List.mem_cons_self ..) hvar
        · intro τ' hc'
          exact Signature.wf_unique_const
            (TransState.freshConst.wf _ (VerifM.eval.wf hdecl_eval)).namesDisjoint
            (List.mem_cons_self ..) hc'
      · simp only [Formula.eval, Term.eval, Const.denote]
        have : v_e = Term.eval ρ_body.env se := by
          rw [Term.eval_env_agree hse_wf (Env.agreeOn_symm hagreeOn_body_e)]
          exact heval_e.symm
        simpa [ρ_body, Env.updateConst] using this
    have hbwf₂ : Bindings.wf ((x, v) :: B) st₂.decls := Bindings.wf_cons hbwf_e
    have hρ_agree : Env.agreeOn (Signature.ofConsts (B.map Prod.snd)) ρ_body.env ρ.env := by
      constructor
      · intro y hy
        cases hy
      · constructor
        · intro y' hy'
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy'
          exact ((hagreeOn_e.2.1 p.2 (hbwf p hp)).trans
            (hagreeOn_body_e.2.1 p.2 (hbwf_e p hp))).symm
        · constructor <;> intro z hz <;> cases hz
    have hρ_body_lookup : ρ_body.env.consts .value v.name = v_e := by
      simp [ρ_body, VerifM.Env.updateConst, Env.updateConst]
    have hagree_body : Bindings.agreeOnLinked ((x, v) :: B) ρ_body.env γ_body := by
      have h := Bindings.agreeOnLinked_cons (x := x) (γ := γ) hagree hρ_agree (hvty := (rfl : v.sort = .value))
      rwa [hρ_body_lookup] at h
    have hts_body : Bindings.typedSubst Θ ((x, v) :: B) (Γ.extend x e.ty) γ_body :=
      Bindings.typedSubst_cons hts htyping_e
    refine ihBody Θ R (Finmap.erase x S) ((x, v) :: B) (Γ.extend x e.ty) st₂ ρ_body γ_body _ _
      (VerifM.eval.decls_grow ρ_body hΨ_body) hagree_body hbwf₂ hts_body
      (SpecMap.wfIn_erase hSwf) ?_
    intro v' ρ' st' se' hΨ hs hw ht
    obtain ⟨_, _, hΨ'⟩ := hΨ
    exact hpost v' ρ' st' se' hΨ' hs hw ht

theorem compileIfThenElse_correct (cond thn els : Expr) (ty : TinyML.Typ)
    (ihCond : correctExpr cond) (ihThn : correctExpr thn) (ihEls : correctExpr els) :
    correctExpr (.ifThenElse cond thn els ty) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  simp only [Expr.ty] at hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  have heval_cond : (compile Θ S B Γ cond).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_if <| SpecMap.satisfiedBy_dup.trans <|
    ihCond Θ (S.satisfiedBy Θ γ ∗ R) S B Γ st ρ γ _ _
    (VerifM.eval.decls_grow ρ heval_cond) hagree hbwf hts hSwf ?_
  intro v_c ρ_c st₁ sc hΨ_c hsc_wf heval_c htypc
  obtain ⟨hdecls_c, hagreeOn_c, hΨ_c⟩ := hΨ_c
  have hagree_c := Bindings.agreeOnLinked_env_agree hagree hagreeOn_c hbwf
  have hbwf_c : B.wf st₁.decls := fun p hp => hdecls_c.consts _ (hbwf p hp)
  obtain ⟨hcond_bool, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
  obtain ⟨hthn_ty, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
  obtain ⟨hels_ty, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
  have heval_branches : (VerifM.all [true, false]).eval st₁ ρ_c _ := VerifM.eval_bind _ _ _ _ hΨ_c
  have hall := VerifM.eval_all heval_branches
  have htrue := hall true (by simp)
  have hfalse := hall false (by simp)
  have hwf_ne : (Formula.not (Formula.eq .value sc (.unop .ofBool (.const (.b false))))).wfIn st₁.decls := by
    simp only [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, _root_.and_true]; exact hsc_wf
  have hwf_eq : (Formula.eq .value sc (.unop .ofBool (.const (.b false) : Term .bool))).wfIn st₁.decls := by
    simp only [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, _root_.and_true]; exact hsc_wf
  have htrue_cont := VerifM.eval_assumePure (VerifM.eval_bind _ _ _ _ htrue)
  have hfalse_cont := VerifM.eval_assumePure (VerifM.eval_bind _ _ _ _ hfalse)
  let φ_eq : Formula := .eq .value sc (.unop .ofBool (.const (.b false) : Term .bool))
  let st_thn : TransState := { st₁ with asserts := φ_eq.not :: st₁.asserts }
  let st_els : TransState := { st₁ with asserts := φ_eq :: st₁.asserts }
  by_cases hvc_false : v_c = .bool false
  · subst hvc_false
    have heval_els : (compile Θ S B Γ els).eval st_els ρ_c Ψ :=
      hfalse_cont hwf_eq (by
        simp only [Formula.eval, Term.eval, UnOp.eval, Const.denote]
        exact heval_c)
    exact SpatialContext.wp_if_false <| ihEls Θ R S B Γ st_els ρ_c γ Ψ Φ heval_els hagree_c hbwf_c hts hSwf
      (fun v ρ' st' se hΨ hs hw ht => hpost v ρ' st' se hΨ hs hw (hels_ty ▸ ht))
  · have hvc_true : v_c = .bool true := by
      rw [hcond_bool] at htypc
      cases htypc with
      | bool b => cases b with
        | false => exact absurd rfl hvc_false
        | true  => rfl
    subst hvc_true
    have heval_ne : sc.eval ρ_c.env ≠ Runtime.Val.bool false := by rw [heval_c]; simp
    have heval_thn : (compile Θ S B Γ thn).eval st_thn ρ_c Ψ :=
      htrue_cont hwf_ne (by
        simp only [Formula.eval, Term.eval, UnOp.eval, Const.denote]
        exact heval_ne)
    exact SpatialContext.wp_if_true <| ihThn Θ R S B Γ st_thn ρ_c γ Ψ Φ heval_thn hagree_c hbwf_c hts hSwf
      (fun v ρ' st' se hΨ hs hw ht => hpost v ρ' st' se hΨ hs hw (hthn_ty ▸ ht))

theorem compileApp_correct (fn : Expr) (args : List Expr) (aty : TinyML.Typ)
    (ihArgs : correctExprs args) :
    correctExpr (.app fn args aty) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  simp only [Expr.ty] at hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst, List.map_map]
  cases fn with
  | var f fty =>
    simp only [compile] at heval
    obtain ⟨spec, hlookup, heval⟩ := VerifM.eval_bind_expectSome heval
    have heval_args : (compileExprs Θ S B Γ args).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine SpecMap.project (P := st.sl ρ ∗ (S.satisfiedBy Θ γ ∗ R)) Θ S γ ?_ hlookup ?_
    · istart
      iintro ⟨_, □HS, _⟩
      iexact HS
    · intro fval hγf
      simp [Expr.runtime, Runtime.Expr.subst, hγf]
      refine SpatialContext.wp_bind_app ?_
      have hctx :
          spec.isPrecondFor Θ fval ∗ (st.sl ρ ∗ (S.satisfiedBy Θ γ ∗ R)) ⊢
            st.sl ρ ∗ (S.satisfiedBy Θ γ ∗ (spec.isPrecondFor Θ fval ∗ R)) := by
        istart
        iintro ⟨□Hspec, Howns, □HS, HR⟩
        isplitl [Howns]
        · iexact Howns
        · isplitl []
          · iexact HS
          · isplitl []
            · iexact Hspec
            · iexact HR
      refine hctx.trans <| ihArgs Θ (spec.isPrecondFor Θ fval ∗ R) S B Γ st ρ γ _ _
        (VerifM.eval.decls_grow ρ heval_args) hagree hbwf hts hSwf ?_
      intro vs ρ_args st_args sargs hΨ_args hsargs_wf heval_sargs htyping_args
      obtain ⟨_, _, hΨ_args⟩ := hΨ_args
      let typedArgs := (args.map Expr.ty).zip sargs
      have hlen_sargs : sargs.length = vs.length := by
        simpa [Terms.Eval] using List.Forall₂.length_eq heval_sargs
      have hlen_typed : (args.map Expr.ty).length = sargs.length := by
        calc
          (args.map Expr.ty).length = vs.length := by simpa using htyping_args.length_eq.symm
          _ = sargs.length := hlen_sargs.symm
      obtain ⟨hret_eq, hΨ_args⟩ := VerifM.eval_bind_expectEq hΨ_args
      obtain ⟨_, hΨ_args⟩ := VerifM.eval_bind_expectEq hΨ_args
      have hwf_pred : spec.pred.wfIn ((Signature.ofVars FiniteSubst.id.dom).declVars (Spec.argVars spec.args)) := by
        simpa [Spec.wfIn, FiniteSubst.id, Signature.empty, Signature.ofVars] using hSwf f spec hlookup
      have hid_wf : FiniteSubst.id.wf st_args.decls := FiniteSubst.id_wf st_args.decls
      have htypedArgs_wf : ∀ p ∈ typedArgs, p.2.wfIn st_args.decls := by
        intro p hp
        have hp'' : p.2 ∈ sargs := (List.of_mem_zip hp).2
        exact hsargs_wf _ hp''
      have hcall_eval : VerifM.eval (Spec.call Θ FiniteSubst.id spec typedArgs) st_args ρ_args
          (fun p st' ρ' => VerifM.eval (pure p.2) st' ρ' Ψ) := VerifM.eval_bind _ _ _ _ hΨ_args
      have hcall := Spec.call_correct Θ spec FiniteSubst.id typedArgs st_args ρ_args
        (fun p st' ρ' => VerifM.eval (pure p.2) st' ρ' Ψ) Φ R
        hwf_pred
        (by simpa [FiniteSubst.id, Signature.ofVars] using Signature.wf_empty)
        hid_wf htypedArgs_wf hcall_eval
        (fun v st' ρ' t hΨ hwf heval hty =>
          hpost v ρ' st' t (VerifM.eval_ret hΨ) hwf heval (hret_eq ▸ hty))
      obtain ⟨hsub_ty, happly⟩ := hcall
      have hsub_ty' : @TinyML.Typ.SubList Θ (args.map Expr.ty) (spec.args.map Prod.snd) := by
        simpa [typedArgs, List.map_fst_zip (Nat.le_of_eq hlen_typed)] using hsub_ty
      have htyped : TinyML.ValsHaveTypes Θ vs (spec.args.map Prod.snd) :=
        TinyML.ValsHaveTypes_sub htyping_args hsub_ty'
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
          st_args.sl ρ_args ∗ R ⊢
            PredTrans.apply (fun r => ⌜TinyML.ValHasType Θ r spec.retTy⌝ -∗ Φ r) spec.pred
              (Spec.argsEnv VerifM.Env.empty spec.args vs) := by
        rw [heval_sargs_map] at happly
        exact happly.trans <| PredTrans.apply_env_agree hwf_pred <|
          Spec.argsEnv_agreeOn (Δ := Signature.empty)
            (ρ₁ := VerifM.Env.withEnv ρ_args (FiniteSubst.id.subst.eval ρ_args.env))
            (ρ₂ := VerifM.Env.empty)
            (by exact ⟨nofun, nofun, nofun, nofun⟩) spec.args vs
            (by have := htyped.length_eq; simp [List.length_map] at this; omega)
      have happly'' :
          st_args.sl ρ_args ∗
              (S.satisfiedBy Θ γ ∗ R) ⊢
            PredTrans.apply (fun r => ⌜TinyML.ValHasType Θ r spec.retTy⌝ -∗ Φ r) spec.pred
              (Spec.argsEnv VerifM.Env.empty spec.args vs) := by
        have hdrop :
            st_args.sl ρ_args ∗
                (S.satisfiedBy Θ γ ∗ R) ⊢
              st_args.sl ρ_args ∗ R := by
          simpa [sep_assoc] using
            (SpecMap.satisfiedBy_drop
              (A := st_args.sl ρ_args)
              (Θ := Θ) (S := S) (γ := γ)
              (R := R))
        exact hdrop.trans happly'
      refine SpatialContext.wp_val ?_
      unfold Spec.isPrecondFor
      istart
      iintro ⟨Howns, □HS, □Hspec, HR⟩
      ispecialize Hspec $$ %Φ
      ispecialize Hspec $$ %vs
      iapply Hspec
      · ipure_intro
        exact htyped
      · iapply happly''
        isplitl [Howns]
        · iexact Howns
        · isplitl []
          · iexact HS
          · iexact HR
  | _ =>
    simp only [compile] at heval
    exact (VerifM.eval_fatal heval).elim

theorem compileTuple_correct (es : List Expr)
    (ihEs : correctExprs es) :
    correctExpr (.tuple es) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  simp only [Expr.ty] at hpost
  unfold Expr.runtime
  simp only [Runtime.Expr.subst, List.map_map]
  simp only [compile] at heval
  have heval_es : (compileExprs Θ S B Γ es).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_tuple <| ihEs Θ R S B Γ st ρ γ _ _
    (VerifM.eval.decls_grow ρ heval_es) hagree hbwf hts hSwf ?_
  intro vs ρ' st' terms hΨ hwf_terms heval_terms htyping
  obtain ⟨_, _, hΨ⟩ := hΨ
  obtain hΨ := VerifM.eval_ret hΨ
  have heval_tuple : (Term.unop .ofValList (Terms.toValList terms)).eval ρ'.env = Runtime.Val.tuple vs := by
    simp [Term.eval, UnOp.eval, Terms.toValList_eval heval_terms]
  have hwf_tuple : (Term.unop UnOp.ofValList (Terms.toValList terms)).wfIn st'.decls := by
    simp only [Term.wfIn]
    exact ⟨trivial, Terms.toValList_wfIn hwf_terms⟩
  exact SpecMap.satisfiedBy_drop.trans <| SpatialContext.wp_tuple <|
    hpost (Runtime.Val.tuple vs) ρ' st' (.unop .ofValList (Terms.toValList terms))
      hΨ hwf_tuple heval_tuple (.tuple htyping)

theorem compileMatch_correct (scrut : Expr) (branches : List (Binder × Expr)) (ty : TinyML.Typ)
    (ihScrut : correctExpr scrut) (ihBranches : correctBranches branches) :
    correctExpr (.match_ scrut branches ty) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  simp only [Expr.ty] at hpost
  unfold Expr.runtime
  simp only [Expr.branchListRuntime_eq_map, Runtime.Expr.subst, List.map_map]
  simp only [compile] at heval
  have heval_scrut : (compile Θ S B Γ scrut).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpatialContext.wp_bind_match <| SpecMap.satisfiedBy_dup.trans <|
    ihScrut Θ (S.satisfiedBy Θ γ ∗ R) S B Γ st ρ γ _ _
      (VerifM.eval.decls_grow ρ heval_scrut) hagree hbwf hts hSwf ?_
  intro v_scrut ρ_scrut st_scrut se_scrut hΨ_scrut hse_wf heval_se htype_scrut
  obtain ⟨hdecls_scrut, hagreeOn_scrut, hΨ_scrut⟩ := hΨ_scrut
  cases hscrut_ty : scrut.ty with
  | unit | bool | int | arrow _ _ | ref _ | empty | value | tuple _ | tvar _ | named _ _ =>
    simp only [hscrut_ty] at hΨ_scrut
    exact (VerifM.eval_fatal hΨ_scrut).elim
  | sum ts =>
    simp [hscrut_ty] at hΨ_scrut htype_scrut
    by_cases hlen : ts.length ≠ branches.length
    · simp [hlen] at hΨ_scrut
      exact (VerifM.eval_fatal hΨ_scrut).elim
    · push_neg at hlen
      by_cases htys : ∀ br ∈ branches, br.2.ty = ty
      · have hΨ_scrut' :
            (do
              let i ← VerifM.all (List.range (compileBranches Θ S B Γ se_scrut ts branches 0).length)
              match (compileBranches Θ S B Γ se_scrut ts branches 0)[i]? with
              | some m => m
              | none => VerifM.fatal "match branch index out of range").eval st_scrut ρ_scrut Ψ := by
          simpa [if_pos hlen, if_pos htys] using hΨ_scrut
        have hcb := compileBranches_spec Θ S B Γ se_scrut ts branches 0
        have hactions_len := hcb.1
        have heval_all := VerifM.eval_bind _ _ _ _ hΨ_scrut'
        have hall := VerifM.eval_all heval_all
        cases htype_scrut with
        | inj ht_tag htype_payload =>
          rename_i tag ty_payload v_payload
          have htag_bound : tag < ts.length := by
            exact (List.getElem?_eq_some_iff.mp ht_tag).1
          have htag_branches : tag < branches.length := hlen ▸ htag_bound
          have htag_range : tag ∈ List.range (compileBranches Θ S B Γ se_scrut ts branches 0).length := by
            rw [hactions_len]
            exact List.mem_range.mpr htag_branches
          have heval_tag := hall tag htag_range
          have hcb_get := hcb.2 tag htag_branches
          simp [hcb_get, show branches[tag]? = some branches[tag] from
            List.getElem?_eq_some_iff.mpr ⟨htag_branches, rfl⟩] at heval_tag
          have hty_eq : ts[tag]?.getD .value = ty_payload := by
            simp [ht_tag]
          rw [hty_eq] at heval_tag
          have hagree_scrut := Bindings.agreeOnLinked_env_agree hagree hagreeOn_scrut hbwf
          have hbwf_scrut : B.wf st_scrut.decls := fun p hp => hdecls_scrut.consts _ (hbwf p hp)
          have hbranch_wp := ihBranches Θ R S B Γ se_scrut ts.length ts 0
            st_scrut ρ_scrut γ Ψ Φ
            hagree_scrut hbwf_scrut hts hSwf hse_wf
            (fun j hj v ρ' st' se hΨ hse_wf hse_eval htyped =>
              SpecMap.satisfiedBy_drop.trans <| hpost v ρ' st' se hΨ hse_wf hse_eval
                ((htys (branches[j]) (List.getElem_mem _)) ▸ htyped))
            tag htag_branches (by simpa [Nat.zero_add, hty_eq] using heval_tag)
          have hsc_eval : se_scrut.eval ρ_scrut.env = Runtime.Val.inj tag ts.length v_payload :=
            heval_se
          have hpayload_ty : TinyML.ValHasType Θ v_payload (ts[tag]?.getD .value) := by
            simpa [hty_eq] using htype_payload
          have hbranch := hbranch_wp v_payload ((Nat.zero_add tag).symm ▸ hsc_eval)
            ((Nat.zero_add tag).symm ▸ hpayload_ty)
          exact SpatialContext.wp_match
            (by simpa [Nat.zero_add] using hbranch)
            (by simp [htag_branches])
      · have hΨ_bad : (VerifM.fatal "match branch type annotation mismatch").eval st_scrut ρ_scrut Ψ := by
          simpa [if_pos hlen, if_neg htys] using hΨ_scrut
        exact (VerifM.eval_fatal hΨ_bad).elim

theorem compileSingleBranch_correct (binder : Binder) (body : Expr)
    (ihBody : correctExpr body) :
    correctBranch (binder, body) := by
  intro Θ R S B Γ sc n i ty_i st ρ γ Ψ Φ heval hagree hbwf hts hSwf hsc_wf hpost payload hsc_eval htype_payload
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
      fresh_not_mem _ _ (addNumbers_injective _)
    have hformula_wf : (Formula.eq .value sc
        (.unop (.mkInj i n) (.const (.uninterpreted xv.name .value)))).wfIn st₁.decls := by
      simp only [Formula.wfIn, Term.wfIn, Const.wfIn]
      refine ⟨Term.wfIn_mono sc hsc_wf (Signature.Subset.subset_addConst _ _)
        (TransState.freshConst.wf _ (VerifM.eval.wf heval_decl)).namesDisjoint, trivial, ?_⟩
      refine ⟨List.mem_cons_self .., ?_, ?_⟩
      · intro τ' hvar
        exact Signature.wf_no_var_of_const
          (TransState.freshConst.wf _ (VerifM.eval.wf heval_decl)).namesDisjoint
          (List.mem_cons_self ..) hvar
      · intro τ' hc'
        exact Signature.wf_unique_const
          (TransState.freshConst.wf _ (VerifM.eval.wf heval_decl)).namesDisjoint
          (List.mem_cons_self ..) hc'
    have hsc_eval_ρ₁ : sc.eval ρ₁.env = sc.eval ρ.env :=
      Term.eval_env_agree hsc_wf (Env.agreeOn_symm (agreeOn_update_fresh_const hxv_fresh))
    have hformula_eval : Formula.eval ρ₁.env
        (Formula.eq .value sc (.unop (.mkInj i n) (.const (.uninterpreted xv.name .value)))) := by
      simp [Formula.eval, Term.eval, UnOp.eval]
      rw [hsc_eval_ρ₁, hsc_eval]
      simp [ρ₁, Env.updateConst]
    have heval_assumeAll := hassume hformula_wf hformula_eval
    have hxv_wf : (Term.const (.uninterpreted xv.name .value)).wfIn st₁.decls := by
      simp only [Term.wfIn, Const.wfIn]
      refine ⟨List.mem_cons_self .., ?_, ?_⟩
      · intro τ' hvar
        exact Signature.wf_no_var_of_const
          (TransState.freshConst.wf _ (VerifM.eval.wf heval_decl)).namesDisjoint
          (List.mem_cons_self ..) hvar
      · intro τ' hc'
        exact Signature.wf_unique_const
          (TransState.freshConst.wf _ (VerifM.eval.wf heval_decl)).namesDisjoint
          (List.mem_cons_self ..) hc'
    have hxv_eval : (Term.const (.uninterpreted xv.name .value)).eval ρ₁.env = payload := by
      simp [Term.eval, Const.denote, ρ₁, Env.updateConst]
    have hassume_bind₂ := VerifM.eval_bind _ _ _ _ heval_assumeAll
    obtain ⟨st₂, hst₂_decls, hst₂_owns, heval_body'⟩ := VerifM.eval_assumeAll hassume_bind₂
      (fun φ hφ => typeConstraints_wfIn hxv_wf φ hφ)
      (fun φ hφ => typeConstraints_hold hxv_eval htype_payload φ hφ)
    have hst₂_owns_eq : st₂.owns = st.owns := hst₂_owns
    have hinterp_eq : SpatialContext.interp ρ.env st.owns ⊢ SpatialContext.interp ρ₁.env st.owns :=
      (SpatialContext.interp_env_agree (VerifM.eval.wf heval_decl).ownsWf
        (agreeOn_update_fresh_const hxv_fresh)).1
    have hagreeOn_st : Env.agreeOn st.decls ρ.env ρ₁.env :=
      agreeOn_update_fresh_const hxv_fresh
    cases hname : binder.name with
    | none =>
      simp [hname] at heval_body'
      have hagree₁ : B.agreeOnLinked ρ₁.env γ :=
        Bindings.agreeOnLinked_env_agree hagree hagreeOn_st hbwf
      have hbwf₁ : B.wf st₂.decls := hst₂_decls ▸ fun p hp => List.Mem.tail _ (hbwf p hp)
      have hts₁ : B.typedSubst Θ (Γ.extendBinder binder ty_i) γ := by
        simpa [TinyML.TyCtx.extendBinder, hname] using hts
      have heval_body'' : (compile Θ S B (Γ.extendBinder binder ty_i) body).eval st₂ ρ₁ Ψ := by
        simpa [ρ₁, xv, hint, hname] using heval_body'
      rw [Binder.runtime_of_name_none hname]
      simp only [Runtime.Expr.subst_fix]
      apply BIBase.Entails.trans _ wp.app_lambda_single
      change SpatialContext.interp ρ.env st.owns ∗ (S.satisfiedBy Θ γ ∗ R) ⊢
        wp
          ((body.runtime.subst ((γ.remove' .none).removeAll' [.none])).subst
            ((Runtime.Subst.id.update' .none Runtime.Val.unit).updateAll' [.none] [payload]))
          Φ
      rw [Runtime.Expr.subst_fix_comp body.runtime .none [.none] γ Runtime.Val.unit [payload] rfl]
      simp only [Runtime.Subst.update', Runtime.Subst.updateAll'_cons, Runtime.Subst.updateAll'_nil_left]
      exact (sep_mono_l hinterp_eq).trans <| SpecMap.satisfiedBy_dup.trans <| (hst₂_owns_eq ▸
        by simpa [Runtime.Subst.update] using
          ihBody Θ (S.satisfiedBy Θ γ ∗ R) S B (Γ.extendBinder binder ty_i) _ ρ₁ γ Ψ Φ
            heval_body'' hagree₁ hbwf₁ hts₁ hSwf
            (fun v ρ' st' se hΨ hs hw ht =>
              by simpa [hty] using hpost v ρ' st' se hΨ hs hw ht))
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
          · constructor <;> intro z hz <;> cases hz
      have hbwf₂ : Bindings.wf ((x, xv) :: B) st₂.decls := hst₂_decls ▸ Bindings.wf_cons hbwf
      have hρ₁_lookup : ρ₁.env.consts .value xv.name = payload := by
        simp [ρ₁, VerifM.Env.updateConst, Env.updateConst]
      have hagree₁ : Bindings.agreeOnLinked ((x, xv) :: B) ρ₁.env (Runtime.Subst.update γ x payload) := by
        have h := Bindings.agreeOnLinked_cons (x := x) (v := xv) (γ := γ) hagree hagreeOn_B (hvty := rfl)
        rwa [hρ₁_lookup] at h
      have hts₁ : Bindings.typedSubst Θ ((x, xv) :: B) (Γ.extendBinder binder ty_i) (Runtime.Subst.update γ x payload) := by
        simpa [TinyML.TyCtx.extendBinder, hname, hty] using (Bindings.typedSubst_cons hts htype_payload)
      have heval_body'' :
          (compile Θ (Finmap.erase x S) ((x, xv) :: B) (Γ.extendBinder binder ty_i) body).eval st₂ ρ₁ Ψ := by
        simpa [ρ₁, xv, hint, TinyML.TyCtx.extendBinder, hname] using heval_body'
      rw [Binder.runtime_of_name_some hname]
      simp only [Runtime.Expr.subst_fix]
      apply BIBase.Entails.trans _ wp.app_lambda_single
      change SpatialContext.interp ρ.env st.owns ∗ (S.satisfiedBy Θ γ ∗ R) ⊢
        wp
          ((body.runtime.subst ((γ.remove' .none).removeAll' [.named x])).subst
            ((Runtime.Subst.id.update' .none Runtime.Val.unit).updateAll' [.named x] [payload]))
          Φ
      rw [Runtime.Expr.subst_fix_comp body.runtime .none [.named x] γ Runtime.Val.unit [payload] rfl]
      simp only [Runtime.Subst.update', Runtime.Subst.updateAll'_cons, Runtime.Subst.updateAll'_nil_left]
      exact (sep_mono_l hinterp_eq).trans <| SpecMap.satisfiedBy_dup.trans <|
        (SpecMap.satisfiedBy_weaken SpecMap.satisfiedBy_erase).trans <| by
          simpa [hst₂_owns_eq, Runtime.Subst.update] using
          ihBody Θ (S.satisfiedBy Θ γ ∗ R) (Finmap.erase x S) ((x, xv) :: B) (Γ.extendBinder binder ty_i) _ ρ₁
            (Runtime.Subst.update γ x payload) Ψ Φ heval_body'' hagree₁ hbwf₂ hts₁
            (SpecMap.wfIn_erase hSwf)
            (fun v ρ' st' se hΨ hs hw ht =>
              by simpa [hty] using hpost v ρ' st' se hΨ hs hw ht)
  · have hexpect := VerifM.eval_bind _ _ _ _ heval
    exact False.elim (hty (VerifM.eval_expectEq hexpect).1)

theorem compileBranchesCons_correct (b : Binder × Expr) (bs : List (Binder × Expr))
    (ihHead : correctBranch b) (ihTail : correctBranches bs) :
    correctBranches (b :: bs) := by
  intro Θ R S B Γ sc n ts idx st ρ γ Ψ Φ hagree hbwf hts hSwf hsc_wf hpost j hj
  cases j with
  | zero =>
    simp only [Nat.add_zero, List.getElem_cons_zero]
    intro heval
    exact ihHead Θ R S B Γ sc n idx (ts[idx]?.getD .value) st ρ γ Ψ Φ
      heval hagree hbwf hts hSwf hsc_wf (by simpa using hpost 0 hj)
  | succ k =>
    have hk : k < bs.length := by simp at hj; omega
    have hidx : idx + (k + 1) = (idx + 1) + k := by omega
    simp only [hidx, List.getElem_cons_succ]
    exact ihTail Θ R S B Γ sc n ts (idx + 1) st ρ γ Ψ Φ
      hagree hbwf hts hSwf hsc_wf
      (by
        intro j hj' v ρ' st' se hΨ hse_wf hse_eval htyped
        simpa [Nat.add_assoc] using hpost (j + 1) (by simpa using hj') v ρ' st' se hΨ hse_wf hse_eval htyped)
      k hk

theorem compileExprsCons_correct (e : Expr) (rest : List Expr)
    (ihE : correctExpr e) (ihRest : correctExprs rest) :
    correctExprs (e :: rest) := by
  intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
  simp only [compileExprs] at heval
  simp only [List.map, wps_cons]
  have heval_rest : (compileExprs Θ S B Γ rest).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
  refine SpecMap.satisfiedBy_dup.trans <|
    ihRest Θ (S.satisfiedBy Θ γ ∗ R) S B Γ st ρ γ _ _
      (VerifM.eval.decls_grow ρ heval_rest) hagree hbwf hts hSwf ?_
  intro vs ρ_vs st_vs rest_terms hΨ_vs hwf_rest heval_rest htyping_vs
  obtain ⟨hdecls_vs, hagreeOn_vs, hΨ_vs⟩ := hΨ_vs
  have hagree_vs : B.agreeOnLinked ρ_vs.env γ :=
    Bindings.agreeOnLinked_env_agree hagree hagreeOn_vs hbwf
  have hbwf_vs : B.wf st_vs.decls := fun p hp => hdecls_vs.consts _ (hbwf p hp)
  have heval_e : (compile Θ S B Γ e).eval st_vs ρ_vs _ := VerifM.eval_bind _ _ _ _ hΨ_vs
  refine ihE Θ (S.satisfiedBy Θ γ ∗ R) S B Γ st_vs ρ_vs γ _ _
    (VerifM.eval.decls_grow ρ_vs heval_e) hagree_vs hbwf_vs hts hSwf ?_
  intro v ρ' st' se hΨ_e hse_wf heval_se htyping_e
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
  exact hpost (v :: vs) ρ' st' (se :: rest_terms) hΨ_e hwf_cons heval_cons (.cons htyping_e htyping_vs)


/-! #### Correctness Theorem -/

mutual
theorem compile_correct (e : Expr) : correctExpr e := by
  cases e with
  | const c =>
    simpa using compileConst_correct c
  | var x vty =>
    simpa using compileVar_correct x vty
  | inj tag arity payload =>
    simpa using compileInj_correct tag arity payload (compile_correct payload)
  | cast e ty =>
    simpa using compileCast_correct e ty (compile_correct e)
  | assert e =>
    simpa using compileAssert_correct e (compile_correct e)
  | fix self args retTy body =>
    simpa using compileFix_correct self args retTy body
  | ref e =>
    simpa using compileRef_correct e (compile_correct e)
  | deref e ty =>
    simpa using compileDeref_correct e ty (compile_correct e)
  | store loc val =>
    simpa using compileStore_correct loc val (compile_correct val) (compile_correct loc)
  | unop op e uty =>
    simpa using compileUnop_correct op e uty (compile_correct e)
  | binop op l r bty =>
    simpa using compileBinop_correct op l r bty (compile_correct r) (compile_correct l)
  | letIn b e body =>
    simpa using compileLetIn_correct b e body (compile_correct e) (compile_correct body)
  | ifThenElse cond thn els ty =>
    simpa using compileIfThenElse_correct cond thn els ty
      (compile_correct cond) (compile_correct thn) (compile_correct els)
  | app fn args aty =>
    simpa using compileApp_correct fn args aty (compileExprs_correct args)
  | tuple es =>
    simpa using compileTuple_correct es (compileExprs_correct es)
  | match_ scrut branches ty =>
    simpa using compileMatch_correct scrut branches ty
      (compile_correct scrut) (compileBranches_correct branches)

theorem compileBranch_correct (branch : Binder × Expr) : correctBranch branch := by
  obtain ⟨binder, body⟩ := branch
  simpa using compileSingleBranch_correct binder body (compile_correct body)

theorem compileBranches_correct (branches : List (Binder × Expr)) : correctBranches branches := by
  match branches with
  | [] =>
    intro Θ R S B Γ sc n ts idx st ρ γ Ψ Φ hagree hbwf hts hSwf hsc_wf hpost j hj
    exact absurd hj (Nat.not_lt_zero _)
  | b :: bs =>
    simpa using compileBranchesCons_correct b bs
      (compileBranch_correct b) (compileBranches_correct bs)

theorem compileExprs_correct (es : List Expr) : correctExprs es := by
  match es with
  | [] =>
    intro Θ R S B Γ st ρ γ Ψ Φ heval hagree hbwf hts hSwf hpost
    simp only [compileExprs] at heval
    simp only [List.map, wps]
    obtain heval := VerifM.eval_ret heval
    exact hpost [] ρ st [] heval (by simp) .nil .nil
  | e :: rest =>
    simpa using compileExprsCons_correct e rest
      (compile_correct e) (compileExprs_correct rest)
end

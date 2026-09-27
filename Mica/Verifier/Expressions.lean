-- SUMMARY: Compilation of typed TinyML expressions into verifier terms, with weakest-precondition correctness proofs.
import Mica.SourceTinyML.Typed
import Mica.SourceTinyML.Typing
import Mica.TinyML.OpSem
import Mica.Verifier.PrimitiveLaws
import Mica.Verifier.FiniteSubst
import Mica.Verifier.Monad
import Mica.Verifier.Assertions
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.Specifications
import Mica.Verifier.Compilation
import Mica.Verifier.Ghost
import Mica.Engine.Driver
import Mica.Base.Fresh
import Mica.Verifier.Intrinsic
import Mica.Verifier.RelationalEncoding.Variables

open Verifier (State)

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]
open Typed
open Verifier (Scope)

/-! ## Expression Compilation

Compiles TinyML expressions to SMT terms via `VerifM`, out of the pieces
`Verifier/Compilation.lean` provides. Correctness is stated against the
weakest-precondition calculus. -/

/-- The scope a specified function literal's body is compiled in: the closure's
    own binding, then its parameters. -/
def fixScope (S : Scope) (self : Binder) (fv : Decl.Const) (selfTy : TinyML.Typ)
    (argNames : List String) (argVars : List Decl.Const) (argTys : List TinyML.Typ)
    (ghost : List (String × TinyML.Typ)) (ghostVars : List Decl.Const) : Scope :=
  (S.bindRuntimeBinder self fv selfTy).bindParameters argNames argVars argTys ghost ghostVars

mutual
  def compile (env : Verifier.Env) (S : Scope) : Expr → VerifM (Term .value)
    | .const (.int n)  => pure (.unop .ofInt  (.const (.i n)))
    | .const (.int32 bits) => pure (.unop .ofInt32 (.const (.bv bits)))
    | .const (.int64 bits) => pure (.unop .ofInt64 (.const (.bv bits)))
    | .const (.bool b) => pure (.unop .ofBool (.const (.b b)))
    | .const (.char c) => pure (.unop .ofChar (.const (.char c)))
    | .const (.string s) => pure (.unop .ofString (.const (.str s)))
    | .const (.float b) => pure (.unop .ofFloat (.const (.fp b)))
    | .const .unit     => pure (Term.const .unit)
    | .var x inst vty => do
        let x' ← match S.runtimeBindings.lookup x, S.ghostBindings.lookup x, S.ghostFns.lookup x with
          | some c, _, _ => pure c
          | none, some _, _ => VerifM.fatal s!"ghost variable in a run-time position: {x}"
          | none, none, some _ => VerifM.fatal s!"ghost function in a run-time position: {x}"
          | none, none, none => VerifM.fatal s!"undefined variable: {x}"
        VerifM.expectEq s!"type annotation mismatch for variable: {x}"
          (((S.typingContext x).map (·.instantiate (TinyML.Typ.ofInst inst))).getD .value) vty
        pure (.const (.uninterpreted x'.name .value))
    | .unop op e uty => do
        let se ← compile env S e
        let ty ← VerifM.expectSome
          s!"type error: operator {repr op} cannot be applied to {repr e.ty}"
          (TinyML.UnOp.typeOf op e.ty)
        VerifM.expectEq "unop type annotation mismatch" ty uty
        let t ← VerifM.expectSome
          s!"unsupported unary operator: {repr op}"
          (compileUnop op se)
        pure t
    | .assert e => do
        let sl ← compile env S e
        VerifM.assert (Formula.eq .bool (Term.unop .toBool sl) (Term.const (.b true)))
        pure (Term.const .unit)
    | .binop op l r bty => do
        let sr ← compile env S r
        let sl ← compile env S l
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
    | .letIn .ghost b e body => do
        let se ← compileGhostExpr env S e
        VerifM.expectEq "ghost let type annotation mismatch" b.ty e.ty
        match b.name with
        | none => compile env S body
        | some x =>
          let x' ← VerifM.define (some x) se
          compile env (S.bindGhost x x' e.ty) body
    | .letIn .runtime b e body => do
        let se ← compile env S e
        VerifM.expectEq "let type annotation mismatch" b.ty e.ty
        match b.name with
        | none => compile env S body
        | some x =>
          let x' ← VerifM.define (some x) se
          compile env (S.bindRuntime x x' e.ty) body
    | .letProd names e body => do
        let se ← compile env S e
        let tys ← match e.ty with
          | .tuple tys => pure tys
          | _ => VerifM.fatal "letProd expected tuple type"
        let S' ← compileProductBinders .runtime S names tys se
        compile env S' body
    | .ifThenElse cond thn els ty => do
        let sc ← compile env S cond
        VerifM.expectEq "if condition type mismatch" cond.ty .bool
        VerifM.expectEq "if branch type annotation mismatch" thn.ty ty
        VerifM.expectEq "if branch type annotation mismatch" els.ty ty
        let branch ← VerifM.all [true, false]
        if branch then do
          VerifM.assume (.pure (.not sc.isFalse))
          compile env S thn
        else do
          VerifM.assume (.pure sc.isFalse)
          compile env S els
    | .app fn args gargs aty =>
      -- A function expression whose type carries a specification is applied
      -- through it: the specification is read off the type, and the function
      -- value's own interpretation supplies the call.
      --
      -- The ghost arguments are compiled through the ghost layer, after the
      -- function and immediately before the call. They are erased, so they take
      -- no step of their own, but one may call a ghost function and so move
      -- ownership; that has to happen in the state the call is made in. Only a
      -- specified function declares ghost parameters.
      match fn.ty with
      | .arrow argTys retTy (some s) =>
        -- The specification rides on a type, so nothing has checked it yet.
        match Spec.checkWf s env.signature with
        | .error msg => VerifM.fatal msg
        | .ok () => do
          VerifM.expectEq "app type annotation mismatch" retTy aty
          VerifM.expectEq "specification arity mismatch" s.args.length argTys.length
          let sterms ← compileExprs env S args
          let sargs := (args.map Expr.WithTypeVars.ty).zip sterms
          let _ ← compile env S fn
          let gterms ← compileGhostExprs env S gargs
          let (_, result) ← Spec.call (FiniteSubst.base env.signature) argTys retTy s sargs
            ((gargs.map Expr.WithTypeVars.ty).zip gterms)
          pure result
      | _ =>
        match fn with
        | .prim n inst _ => do
            let i ← VerifM.expectSome s!"unknown primitive `{n}`"
              (env.registry.lookup? n)
            let _ ← VerifM.expectSome
              s!"primitive `{n}` is available in ghost code only" i.mode.runtime?
            let σi : TinyML.TyVar → TinyML.Typ := fun v => (inst.lookup v).getD .empty
            VerifM.expectEq "primitive return type mismatch"
              (TinyML.Typ.subst σi i.retTy) aty
            -- An intrinsic declares no ghost parameter, so a call of one carries
            -- no ghost argument.
            VerifM.expectEq "a primitive takes no ghost argument" gargs.length 0
            let sterms ← compileExprs env S args
            let sargs := (args.map Expr.WithTypeVars.ty).zip sterms
            let (_, result) ← Spec.call (FiniteSubst.base env.signature)
              (i.argTys.map (TinyML.Typ.subst σi)) (TinyML.Typ.subst σi i.retTy) i.spec sargs []
            pure result
        | _ => VerifM.fatal "application of a function without a specification"
    | .prim n _ _ => VerifM.fatal s!"primitive `{n}` must be applied"
    | .tuple es => do
        let terms ← compileExprs env S es
        pure (Term.tuple terms)
    | .inj tag arity payload ty => do
        match injComponents? env.typeDeclarations ty tag arity payload.ty with
        | some _ => do
            let s ← compile env S payload
            pure (.unop (.ofInj tag arity) s)
        | none => VerifM.fatal "injection type annotation mismatch"
    | .match_ scrut branches ty => do
        let sc ← compile env S scrut
        match sumComponents? env.typeDeclarations scrut.ty with
        | some ts =>
          if ts.length ≠ branches.length then VerifM.fatal "match arity mismatch"
          else if ∀ br ∈ branches, br.2.ty = ty then do
            let actions := compileBranches env S sc ts branches 0
            let i ← VerifM.all (List.range actions.length)
            match actions[i]? with
            | some m => m
            | none => VerifM.fatal "match branch index out of range"
          else
            VerifM.fatal "match branch type annotation mismatch"
        | none => VerifM.fatal "match on non-sum type"
    | .ref ownership e => do
        let v ← compile env S e
        let l ← VerifM.decl none .value
        let sl := Term.const (.uninterpreted l.name .value)
        match ownership with
        | .owned => do
            VerifM.assume (.spatial (.pointsTo sl v e.ty))
            VerifM.assumeAll (TinyML.typeConstraints (.owned e.ty) sl)
        | .shared => pure ()
        pure sl
    | .deref e ty => do
        let (ownership, ty') : TinyML.Ownership × TinyML.Typ ← match e.ty with
          | .owned ty' => pure (TinyML.Ownership.owned, ty')
          | .ref ty' => pure (TinyML.Ownership.shared, ty')
          | _ => VerifM.fatal "deref operand is not a reference"
        VerifM.expectEq "deref type annotation mismatch" ty' ty
        let lq ← compile env S e
        match ownership with
        | .owned => do
            let v ← VerifM.findMatchForce .ref lq ty
            VerifM.assume (.spatial (.pointsTo lq v ty))
            pure v
        | .shared => do
            let v ← VerifM.decl none .value
            let sv := Term.const (.uninterpreted v.name .value)
            VerifM.assumeAll (TinyML.typeConstraints ty sv)
            pure sv
    | .store loc val => do
        let (ownership, ty) : TinyML.Ownership × TinyML.Typ ← match loc.ty with
          | .owned ty => pure (TinyML.Ownership.owned, ty)
          | .ref ty => pure (TinyML.Ownership.shared, ty)
          | _ => VerifM.fatal "store location is not a reference"
        VerifM.expectEq "store location type mismatch" ty val.ty
        let v ← compile env S val
        let lq ← compile env S loc
        match ownership with
        | .owned => do
            let _ ← VerifM.findMatchForce .ref lq val.ty
            VerifM.assume (.spatial (.pointsTo lq v val.ty))
        | .shared => pure ()
        pure (Term.const .unit)
    | .arrayMake ownership len init => do
        VerifM.expectEq "array length must be int" len.ty .int
        let s_init ← compile env S init
        let sl ← compile env S len
        VerifM.assert (.binpred .le (.const (.i 0)) (.unop .toInt sl))
        let a ← VerifM.decl none .value
        let sa := Term.const (.uninterpreted a.name .value)
        VerifM.assume (.pure (.eq .int (.unop .arrayLen sa) (.unop .toInt sl)))
        if ownership = .owned then
          let contents := Term.unop .ofVec (.binop .vecMake (.unop .toInt sl) s_init)
          VerifM.acquire (.spatial (.arrayPointsTo sa contents init.ty))
          VerifM.assumeAll (TinyML.typeConstraints (.ownedArray init.ty) sa)
        else
          VerifM.assumeAll (TinyML.typeConstraints (.array init.ty) sa)
        pure sa
    | .arrayLen arr => do
        match arr.ty with
        | .array _ | .ownedArray _ =>
            let sa ← compile env S arr
            pure (.unop .ofInt (.unop .arrayLen sa))
        | _ => VerifM.fatal "Array.length operand is not an array"
    | .arrayGet arr idx ty => do
        let (elemTy, owned) ← match arr.ty with
          | .array elemTy => pure (elemTy, false)
          | .ownedArray elemTy => pure (elemTy, true)
          | _ => VerifM.fatal "Array.get operand is not an array"
        VerifM.expectEq "array get element type mismatch" elemTy ty
        VerifM.expectEq "array index must be int" idx.ty .int
        let si ← compile env S idx
        let sa ← compile env S arr
        VerifM.assertBounds si sa
        if owned then
          let contents ← VerifM.findMatchForce .array sa elemTy
          VerifM.acquire (.spatial (.arrayPointsTo sa contents elemTy))
          pure (.binop .vecGet (.unop .toVec contents) (.unop .toInt si))
        else
          let v ← VerifM.decl none .value
          let sv := Term.const (.uninterpreted v.name .value)
          VerifM.assumeAll (TinyML.typeConstraints ty sv)
          pure sv
    | .arraySet arr idx val => do
        let (elemTy, owned) ← match arr.ty with
          | .array elemTy => pure (elemTy, false)
          | .ownedArray elemTy => pure (elemTy, true)
          | _ => VerifM.fatal "Array.set operand is not an array"
        VerifM.expectEq "array set element type mismatch" elemTy val.ty
        VerifM.expectEq "array index must be int" idx.ty .int
        let sv ← compile env S val
        let si ← compile env S idx
        let sa ← compile env S arr
        VerifM.assertBounds si sa
        if owned then
          let contents ← VerifM.findMatchForce .array sa elemTy
          let contents' := Term.unop .ofVec
            (.terop .vecSet (.unop .toVec contents) (.unop .toInt si) sv)
          VerifM.acquire (.spatial (.arrayPointsTo sa contents' elemTy))
        pure (Term.const .unit)
    | .fix self args retTy spec body =>
        match spec with
        | none => VerifM.fatal "a function value must carry a specification"
        | some s =>
          match extractArgNames args s.args with
          | .error msg => VerifM.fatal msg
          | .ok argNames =>
          match Spec.checkWf s env.signature with
          | .error msg => VerifM.fatal msg
          | .ok () => do
            let argTys := args.map Binder.WithTypeVars.ty
            -- The closure itself is an opaque value; the recursive occurrence is
            -- bound to the same constant inside the body.
            let fv ← VerifM.decl self.name .value
            -- The body is a separate obligation: the specification's precondition
            -- and the argument variables must not leak into the continuation.
            VerifM.seq
              (do
                VerifM.persist
                Spec.implement env.signature argTys s fun argVars ghostVars => do
                  env.lemmas.assumeInstance self.name argVars
                  let se ← compile env (fixScope S self fv (.arrow argTys retTy (some s))
                    argNames argVars argTys s.ghost ghostVars) body
                  VerifM.expectEq "fix: body type does not match the return type" body.ty retTy
                  pure se)
              (pure (.const (.uninterpreted fv.name .value)))

  /-- Compile a single match branch: assume the scrutinee is `ofInj i n payload`, then compile the body. -/
  def compileBranch (env : Verifier.Env) (S : Scope)
      (sc : Term .value) (n : Nat) (i : Nat) (ty_i : TinyML.Typ)
      : Binder × Expr → VerifM (Term .value)
    | (binder, body) => do
        VerifM.expectEq "match binder type annotation mismatch" binder.ty ty_i
        let xv ← VerifM.decl binder.name .value
        VerifM.assume (.pure (.eq .value sc (.unop (.ofInj i n) (.const (.uninterpreted xv.name .value)))))
        VerifM.assumeAll (TinyML.typeConstraints ty_i (.const (.uninterpreted xv.name .value)))
        compile env (S.bindRuntimeBinder binder xv ty_i) body

  def compileBranches (env : Verifier.Env) (S : Scope)
      (sc : Term .value) (ts : List TinyML.Typ) :
      List (Binder × Expr) → Nat → List (VerifM (Term .value))
    | [], _ => []
    | branch :: rest, i =>
      compileBranch env S sc ts.length i (ts[i]?.getD .value) branch
        :: compileBranches env S sc ts rest (i + 1)

  def compileExprs (env : Verifier.Env) (S : Scope) : List Expr → VerifM (List (Term .value))
    | [] => pure []
    | e :: es => do
      let rest ← compileExprs env S es
      let se ← compile env S e
      pure (se :: rest)
end

/-! ### Helper lemmas -/

omit [MicaGS HasLC.hasLC Sig] in
theorem compileBranches_length_get (env : Verifier.Env) (S : Scope)
    (sc : Term .value) (ts : List TinyML.Typ)
    (branches : List (Binder × Expr)) (idx : Nat) :
    (compileBranches env S sc ts branches idx).length = branches.length ∧
    ∀ j, j < branches.length →
      (compileBranches env S sc ts branches idx)[j]? =
        branches[j]?.map (fun branch =>
          compileBranch env S sc ts.length (idx + j) (ts[idx + j]?.getD .value) branch) := by
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


/-! ### Correctness -/

/-! #### Correctness Statements -/

/-- A successful compilation of `e` gives the weakest precondition of the
run-time program `e` erases to, under the typing of everything in scope.

`γg` reads the ghost names the way `γ` reads the run-time ones. No ghost name
occurs in the run-time program, so `γg` substitutes into nothing; it is what
makes the ghost half of the typing free of `ρ`, and therefore carried through
every step of the compilation without transport. -/
def correctExpr (e : Expr) : Prop :=
  ∀ (env : Verifier.Env) (W : TinyML.World) (S : Scope) (γg γ : Runtime.Subst)
    {st : State} {ρ : Env} {Ψ : Term .value → State → Env → Prop} {R : iProp}
    {Φ : Runtime.Val → iProp},
    env.wf W →
    S.wfIn W st.decls ρ γg γ →
    VerifM.eval (compile env S e) st ρ Ψ →
    (∀ v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls → Term.eval ρ' se = v →
      st'.sl W ρ' ∗ TinyML.ValHasType W v e.ty ∗ R ⊢ Φ v) →
    st.sl W ρ ∗ (S.typed W γg γ ∗ R) ⊢ wp W.pctx (e.runtime.subst γ) Φ

def correctBranch (branch : Binder × Expr) : Prop :=
  ∀ (env : Verifier.Env) (W : TinyML.World) (S : Scope) (γg γ : Runtime.Subst)
    (sc : Term .value) (n i : Nat) (ty_i : TinyML.Typ)
    {st : State} {ρ : Env} {Ψ : Term .value → State → Env → Prop} {R : iProp}
    {Φ : Runtime.Val → iProp},
    env.wf W →
    S.wfIn W st.decls ρ γg γ →
    sc.wfIn st.decls →
    VerifM.eval (compileBranch env S sc n i ty_i branch) st ρ Ψ →
    (∀ v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls →
      se.eval ρ' = v → st'.sl W ρ' ∗ TinyML.ValHasType W v branch.2.ty ∗ R ⊢ Φ v) →
    ∀ payload, sc.eval ρ = Runtime.Val.inj i n payload →
      st.sl W ρ ∗ TinyML.ValHasType W payload ty_i ∗ (S.typed W γg γ ∗ R) ⊢
        wp W.pctx (.app ((Runtime.Expr.fix .none [branch.1.runtime] branch.2.runtime).subst γ)
          [.val payload]) Φ

def correctBranches (branches : List (Binder × Expr)) : Prop :=
  ∀ (env : Verifier.Env) (W : TinyML.World) (S : Scope) (γg γ : Runtime.Subst)
    (sc : Term .value) (n : Nat) (ts : List TinyML.Typ) (idx : Nat)
    {st : State} {ρ : Env} {Ψ : Term .value → State → Env → Prop} {R : iProp}
    {Φ : Runtime.Val → iProp},
    env.wf W →
    S.wfIn W st.decls ρ γg γ →
    sc.wfIn st.decls →
    (∀ (j : Nat) (hj : j < branches.length) v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls →
      se.eval ρ' = v → st'.sl W ρ' ∗ TinyML.ValHasType W v (branches[j]).2.ty ∗ R ⊢ Φ v) →
    ∀ (j : Nat) (hj : j < branches.length),
      VerifM.eval (compileBranch env S sc n (idx + j) (ts[idx + j]?.getD .value) branches[j])
        st ρ Ψ →
      ∀ payload, sc.eval ρ = Runtime.Val.inj (idx + j) n payload →
        st.sl W ρ ∗ TinyML.ValHasType W payload (ts[idx + j]?.getD .value) ∗
            (S.typed W γg γ ∗ R) ⊢
          wp W.pctx (.app ((Runtime.Expr.fix .none [(branches[j]).1.runtime]
            (branches[j]).2.runtime).subst γ) [.val payload]) Φ

def correctExprs (es : List Expr) : Prop :=
  ∀ (env : Verifier.Env) (W : TinyML.World) (S : Scope) (γg γ : Runtime.Subst)
    {st : State} {ρ : Env} {Ψ : List (Term .value) → State → Env → Prop} {R : iProp}
    {Φ : List Runtime.Val → iProp},
    env.wf W →
    S.wfIn W st.decls ρ γg γ →
    VerifM.eval (compileExprs env S es) st ρ Ψ →
    (∀ vs ρ' st' terms, Ψ terms st' ρ' →
      (∀ t ∈ terms, t.wfIn st'.decls) →
      Term.evalList ρ' terms vs →
       st'.sl W ρ' ∗ TinyML.ValsHaveTypes W vs (es.map Expr.WithTypeVars.ty) ∗ R ⊢ Φ vs) →
    st.sl W ρ ∗ (S.typed W γg γ ∗ R) ⊢ wps W.pctx (es.map (fun e => e.runtime.subst γ)) Φ

/-! #### Correctness Compatibility Lemmas -/

theorem compileConst_correct (c : TinyML.Const) :
    correctExpr (.const c) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  -- Every constant takes the same value step. The cases differ only in the
  -- runtime value, the term compiled for it, and the lemma typing that value.
  have step : ∀ (ty : TinyML.Typ) (v : Runtime.Val) (t : Term .value),
      (∀ v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls → Term.eval ρ' se = v →
        st'.sl W ρ' ∗ TinyML.ValHasType W v ty ∗ R ⊢ Φ v) →
      Ψ t st ρ → t.wfIn st.decls → Term.eval ρ t = v → (⊢ TinyML.ValHasType W v ty) →
      st.sl W ρ ∗ (S.typed W γg γ ∗ R) ⊢ wp W.pctx (.val v) Φ := by
    intro ty v t hpost hΨ henv.world hev hval
    refine PrimitiveLaws.wp_val ?_
    istart
    iintro ⟨Howns, -, HR⟩
    iapply (hpost v ρ st t hΨ henv.world hev)
    iframe
    exact hval
  cases c <;>
    simp only [compile] at heval <;>
    simp only [Expr.WithTypeVars.ty, Const.ty] at hpost <;>
    simp only [Expr.WithTypeVars.runtime, Runtime.Val.ofConst, Runtime.Expr.subst_val]
  case int n =>
    exact step _ (.int n) _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.eval]) (TinyML.ValHasType.int_intro W n)
  case int32 bits =>
    exact step _ (.int32 bits) _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.eval]) (TinyML.ValHasType.int32_intro W bits)
  case int64 bits =>
    exact step _ (.int64 bits) _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.eval]) (TinyML.ValHasType.int64_intro W bits)
  case bool b =>
    exact step _ (.bool b) _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.eval]) (TinyML.ValHasType.bool_intro W b)
  case char c =>
    exact step _ (.char c) _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.eval]) (TinyML.ValHasType.char_intro W c)
  case string s =>
    exact step _ (.str s) _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.eval]) (TinyML.ValHasType.string_intro W s)
  case float b =>
    exact step _ (.float b) _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.eval]) (TinyML.ValHasType.float_intro W b)
  case unit =>
    exact step _ .unit _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn]) (by simp [Term.eval]) (TinyML.ValHasType.unit_intro W)

theorem compileVar_correct (x : String)
    (inst : List (TinyML.TyVar × TinyML.Typ)) (vty : TinyML.Typ) :
    correctExpr (.var x inst vty) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  simp only [compile] at heval
  obtain ⟨x', hbind, heval⟩ : ∃ x', S.runtimeBindings.lookup x = some x' ∧
      VerifM.eval (do
        VerifM.expectEq s!"type annotation mismatch for variable: {x}"
          (((S.typingContext x).map (·.instantiate (TinyML.Typ.ofInst inst))).getD .value) vty
        pure (Term.const (.uninterpreted x'.name .value))) st ρ Ψ := by
    cases hb : S.runtimeBindings.lookup x with
    | some c =>
      simp only [hb] at heval
      exact ⟨c, rfl, VerifM.eval_ret (VerifM.eval_bind heval)⟩
    | none =>
      cases hg : S.ghostBindings.lookup x with
      | some _ =>
        simp only [hb, hg] at heval
        exact (VerifM.eval_fatal (VerifM.eval_bind heval)).elim
      | none =>
        cases hgf : S.ghostFns.lookup x with
        | some _ =>
          simp only [hb, hg, hgf] at heval
          exact (VerifM.eval_fatal (VerifM.eval_bind heval)).elim
        | none =>
          simp only [hb, hg, hgf] at heval
          exact (VerifM.eval_fatal (VerifM.eval_bind heval)).elim
  obtain ⟨hcheck, hcont⟩ := VerifM.eval_bind_expectEq heval
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst]
  obtain ⟨hsort, hγ⟩ := hS.runtimeLinked x x' hbind
  rw [hγ]
  simp
  obtain ⟨hmem, -⟩ := hS.lookup (Or.inr hbind)
  have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
  have hΨ : Ψ (Term.const (.uninterpreted x'.name .value)) st ρ := VerifM.eval_ret hcont
  have hwfv : (Term.const (.uninterpreted x'.name .value)).wfIn st.decls := by
    cases x' with
    | mk n s =>
      simp only at hsort; subst hsort
      exact Term.const_wfIn_of_mem hwfst hmem
  simp only [Expr.WithTypeVars.ty] at hpost
  cases hΓx : S.typingContext x with
  | none =>
    have hvty : vty = .value := by simpa [hΓx] using hcheck.symm
    subst hvty
    have hvalue : ⊢ TinyML.ValHasType W (ρ.consts .value x'.name) .value := by
      iapply (TinyML.ValHasType.value W (ρ.consts .value x'.name)).2
      ipureintro
      trivial
    have hprep :
        st.sl W ρ ∗ (S.typed W γg γ ∗ R) ⊢
          st.sl W ρ ∗ TinyML.ValHasType W (ρ.consts .value x'.name) .value ∗ R := by
      exact sep_mono_right (sep_mono_left (true_intro.trans hvalue))
    have hpost' :
        st.sl W ρ ∗ TinyML.ValHasType W (ρ.consts .value x'.name) .value ∗ R ⊢
          Φ (ρ.consts .value x'.name) := by
      simpa [hΓx] using
        (hpost (ρ.consts .value x'.name) ρ st (Term.const (.uninterpreted x'.name .value))
          hΨ hwfv (by simp [Term.eval, Const.eval]))
    exact PrimitiveLaws.wp_val <| hprep.trans <| hpost'
  | some s =>
    have htv : s.instantiate (TinyML.Typ.ofInst inst) = vty := by simpa [hΓx] using hcheck
    have hprep :
        st.sl W ρ ∗ (S.typed W γg γ ∗ R) ⊢
          st.sl W ρ ∗ TinyML.ValHasType W (ρ.consts .value x'.name) vty ∗ R := by
      rw [← htv]
      exact sep_mono_right (sep_mono_left
        (Scope.typed_lookup hS (TinyML.Typ.ofInst inst) (Or.inr hbind) hΓx))
    have hpost' :
        st.sl W ρ ∗ TinyML.ValHasType W (ρ.consts .value x'.name) vty ∗ R ⊢
          Φ (ρ.consts .value x'.name) :=
      hpost (ρ.consts .value x'.name) ρ st (Term.const (.uninterpreted x'.name .value))
        hΨ hwfv (by simp [Term.eval, Const.eval])
    exact PrimitiveLaws.wp_val <| hprep.trans <| hpost'

theorem compileInj_correct (tag arity : Nat) (payload : Expr)
    (ty : TinyML.Typ) (ihPayload : correctExpr payload) :
    correctExpr (.inj tag arity payload ty) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  cases hcomp : injComponents? env.typeDeclarations ty tag arity payload.ty with
  | none =>
    simp [hcomp] at heval
    exact (VerifM.eval_fatal heval).elim
  | some ts =>
    obtain ⟨hty, hlen_ts, hget_ts⟩ := injComponents?_eq hcomp
    simp only [hcomp] at heval
    have heval_p : (compile env S payload).eval st ρ _ := VerifM.eval_bind heval
    refine PrimitiveLaws.wp_bind_inj <| ihPayload env W S γg γ (R := R) henv hS (VerifM.eval.decls_grow ρ heval_p) ?_
    intro v_p ρ_p st_p se_p hΨ_p hse_wf_p heval_se_p
    obtain ⟨_hdecls_p, _hagreeOn_p, hΨ_p⟩ := hΨ_p
    obtain hΨ_p := VerifM.eval_ret hΨ_p
    simp only [Expr.WithTypeVars.ty] at hpost

    have hinj : TinyML.ValHasType W v_p payload.ty ⊢
        TinyML.ValHasType W (.inj tag arity v_p) ty :=
      (TinyML.ValHasType.inj hlen_ts hget_ts).trans
        (valHasType_sumComponents (henv.typeDeclarations ▸ hty)).2
    have hprep :
        st_p.sl W ρ_p ∗ TinyML.ValHasType W v_p payload.ty ∗ R ⊢
          st_p.sl W ρ_p ∗ TinyML.ValHasType W (.inj tag arity v_p) ty ∗ R :=
      sep_mono_right (sep_mono_left hinj)
    have hpost' :
        st_p.sl W ρ_p ∗ TinyML.ValHasType W (.inj tag arity v_p) ty ∗ R ⊢
          Φ (.inj tag arity v_p) := by
      simpa [hlen_ts] using
        (hpost (.inj tag arity v_p) ρ_p st_p _ hΨ_p
          (by simp only [Term.wfIn]; exact ⟨trivial, hse_wf_p⟩)
          (by simp [Term.eval, UnOp.eval, heval_se_p]))
    exact PrimitiveLaws.wp_inj <| hprep.trans hpost'

theorem compileAssert_correct (e : Expr)
    (ih : correctExpr e) :
    correctExpr (.assert e) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  have heval_e : (compile env S e).eval st ρ _ := VerifM.eval_bind heval
  refine PrimitiveLaws.wp_bind_assert <| ih env W S γg γ (R := R) henv hS (VerifM.eval.decls_grow ρ heval_e) ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se
  obtain ⟨_, _, hΨ_e⟩ := hΨ_e
  let φ := Formula.eq .bool (Term.unop .toBool se) (Term.const (.b true))
  have hwf_φ : φ.wfIn st₁.decls := by
    simpa [φ, Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn] using hse_wf
  have heval_assert : (VerifM.assert φ).eval st₁ ρ_e _ := VerifM.eval_bind hΨ_e
  obtain ⟨hφ, hcont⟩ := VerifM.eval_assert heval_assert hwf_φ
  have hΨ_pure := VerifM.eval_ret hcont
  have hvtrue : v_e = .bool true := by
    simp only [φ, Formula.eval, Term.eval, UnOp.eval, Const.eval] at hφ
    rw [heval_se] at hφ
    cases v_e <;> simp_all
  simp only [Expr.WithTypeVars.ty] at hpost
  subst hvtrue
  have hprep :
      st₁.sl W ρ_e ∗ TinyML.ValHasType W (.bool true) e.ty ∗ R ⊢
        st₁.sl W ρ_e ∗ TinyML.ValHasType W .unit .unit ∗ R :=
    sep_mono_right (sep_mono_left (true_intro.trans (TinyML.ValHasType.unit_intro W)))
  exact PrimitiveLaws.wp_assert <| hprep.trans <| hpost .unit ρ_e st₁ (Term.const .unit) hΨ_pure
    trivial
    (by simp [Term.eval])

/-- Soundness of the body obligation in `compile`'s `fix` case: with the argument
    variables supplied by `Spec.implement_correct`, a successful evaluation of the
    body gives the body's `wp` under the closure's own specification. -/
theorem compileFixBody_correct (env : Verifier.Env) (W : TinyML.World) (henv : env.wf W)
    (S : Scope) (γg γ : Runtime.Subst)
    (self : Binder) (args : List Binder) (retTy : TinyML.Typ) (s : Spec TinyML.Typ)
    (body : Expr) (ih : correctExpr body)
    (argNames : List String) (hext : extractArgNames args s.args = Except.ok argNames)
    (fv : Decl.Const) (fval : Runtime.Val) (vs gs : List Runtime.Val) (P : Runtime.Val → iProp)
    {argVars ghostVars : List Decl.Const} {st' : State} {ρ' : Env} {Q : iProp}
    (hS : S.wfIn W st'.decls ρ' γg γ)
    (hfv_mem : fv ∈ st'.decls.consts) (hfv_sort : fv.sort = .value)
    (hfv_val : ρ'.consts .value fv.name = fval)
    (hargVars_mem : ∀ v ∈ argVars, v ∈ st'.decls.consts)
    (hargVars_sort : ∀ v ∈ argVars, v.sort = .value)
    (hargVars_lookup : List.Forall₂ (fun av val => ρ'.consts .value av.name = val) argVars vs)
    (hghostVars_mem : ∀ v ∈ ghostVars, v ∈ st'.decls.consts)
    (hghostVars_sort : ∀ v ∈ ghostVars, v.sort = .value)
    (hghostVars_lookup : List.Forall₂ (fun gv val => ρ'.consts .value gv.name = val) ghostVars gs)
    (hbody_eval : VerifM.eval
        (do
          env.lemmas.assumeInstance self.name argVars
          let se ← compile env (fixScope S self fv
            (.arrow (args.map Binder.WithTypeVars.ty) retTy (some s)) argNames argVars
            (args.map Binder.WithTypeVars.ty) s.ghost ghostVars) body
          VerifM.expectEq "fix: body type does not match the return type" body.ty retTy
          pure se)
        st' ρ'
        (fun result st'' ρ'' => ∀ X, result.wfIn st''.decls →
          st''.sl W ρ'' ∗ Q ∗
            ((TinyML.ValHasType W (result.eval ρ'') retTy -∗ P (result.eval ρ'')) -∗ X) ⊢ X)) :
    st'.sl W ρ' ∗ TinyML.ValsHaveTypes W vs (args.map Binder.WithTypeVars.ty) ∗
      TinyML.ValsHaveTypes W gs (s.ghost.map Prod.snd) ∗ Q ⊢
      (S.typed W γg γ ∗
        s.isPrecondFor W (TinyML.ValHasType W) (args.map Binder.WithTypeVars.ty) retTy fval) -∗
        wp W.pctx (body.runtime.subst
          ((γ.updateBinder self.runtime fval).updateAllBinder (args.map (·.runtime)) vs)) P := by
  obtain ⟨hargNames_len, hargs_len, hbs_eq⟩ := extractArgNames_spec hext
  set argTys := args.map Binder.WithTypeVars.ty with hargTys_def
  set selfTy : TinyML.Typ := .arrow argTys retTy (some s) with hselfTy_def
  obtain ⟨φs, hbody_eval⟩ := Lemmas.assumeInstance_correct henv.world henv.lemmas hS.agrees
    hargVars_mem hargVars_sort (VerifM.eval_bind hbody_eval)
  -- `sl` does not use the assertions, so `st₀.sl` is `st'.sl`.
  set st₀ : State := { st' with asserts := φs ++ st'.asserts }
  have hcompile := VerifM.eval_bind hbody_eval
  iintro ⟨Howns, #Hvals, #Hgvals, HQ⟩
  ihave %hlen_vals := TinyML.ValsHaveTypes.length_eq $$ Hvals
  ihave %hlen_gvals := TinyML.ValsHaveTypes.length_eq $$ Hgvals
  have hlen_av := hargVars_lookup.length_eq
  have hlen_gv := hghostVars_lookup.length_eq
  simp only [hargTys_def, List.length_map] at hlen_vals hlen_gvals
  have hS_body := (hS.bindRuntimeBinder (b := self) (ty := selfTy) hfv_mem hfv_sort
    hfv_val).bindParameters (names := argNames) (tys := argTys) (ghost := s.ghost)
    (by omega) (by simp [hargTys_def]; omega) (by omega) hargVars_mem hargVars_sort
    hargVars_lookup hghostVars_mem hghostVars_sort hghostVars_lookup
  have hbody_wp := ih env W _ _ _ (st := st₀) (R := Q) (Φ := P) henv hS_body
    (VerifM.eval.decls_grow ρ' hcompile) (by
      intro v ρ'' st'' se hΨ hse_wf heval_se
      obtain ⟨_, _, hΨ⟩ := hΨ
      obtain ⟨hsub, hΨ⟩ := VerifM.eval_bind_expectEq hΨ
      have hΨ' := VerifM.eval_ret hΨ
      rw [← heval_se]
      refine (show st''.sl W ρ'' ∗ TinyML.ValHasType W (se.eval ρ'') body.ty ∗ Q ⊢
          st''.sl W ρ'' ∗ Q ∗
            ((TinyML.ValHasType W (se.eval ρ'') retTy -∗ P (se.eval ρ'')) -∗
              P (se.eval ρ'')) from ?_).trans (hΨ' _ hse_wf)
      iintro ⟨Howns', Hty, HQ'⟩
      iframe Howns' HQ'
      iintro Hwand
      iapply Hwand
      rw [← hsub]
      iexact Hty)
  iintro ⟨#HT, #Hrec⟩
  rw [hbs_eq]
  iapply hbody_wp
  isplitl [Howns]
  · iapply (show st'.sl W ρ' ⊢ st₀.sl W ρ' from .rfl)
    iexact Howns
  isplitr [HQ]
  · iapply (Scope.typed_bindParameters (by omega) hlen_av (by omega) hlen_gv)
    isplitl []
    · iapply Scope.typed_bindRuntimeBinder
      isplitl []
      · iexact HT
      · iapply (TinyML.ValHasType.arrow_some W fval argTys retTy s).2
        iexact Hrec
    · iframe # ∗
  · iexact HQ

theorem compileFix_typed (env : Verifier.Env) (W : TinyML.World) (henv : env.wf W)
    (S : Scope) (γg γ : Runtime.Subst)
    (self : Binder) (args : List Binder) (retTy : TinyML.Typ) (s : Spec TinyML.Typ)
    (body : Expr) (ih : correctExpr body) {st : State} {ρ : Env}
    (hS : S.wfIn W st.decls ρ γg γ)
    {Ψ : Term .value → State → Env → Prop}
    (heval : VerifM.eval (compile env S (.fix self args retTy (some s) body)) st ρ Ψ) :
    S.typed W γg γ ⊢
      TinyML.ValHasType W
        (Runtime.Val.fix self.runtime (args.map (·.runtime))
          (body.runtime.subst ((γ.remove' self.runtime).removeAll' (args.map (·.runtime)))))
        (.arrow (args.map Binder.WithTypeVars.ty) retTy (some s)) := by
  obtain ⟨reg, Θ, Δ, ls, fns, lfs, gls⟩ := env
  obtain ⟨-, -, -, rfl, rfl, -, -, -⟩ := id henv
  simp only [compile] at heval
  cases hext : extractArgNames args s.args with
  | error msg => simp only [hext] at heval; exact (VerifM.eval_fatal heval).elim
  | ok argNames =>
  cases hcheck : Spec.checkWf s W.Δ_spec with
  | error msg => simp only [hext, hcheck] at heval; exact (VerifM.eval_fatal heval).elim
  | ok u =>
  cases u
  simp only [hext, hcheck] at heval
  have hswf : s.wfIn W.Δ_spec := Spec.checkWf_ok hcheck
  obtain ⟨hargNames_len, hargs_len, hbs_eq⟩ := extractArgNames_spec hext
  set argTys := args.map Binder.WithTypeVars.ty with hargTys_def
  set bs := args.map (·.runtime) with hbs_def
  have hbs_runtime : bs = argNames.map Runtime.Binder.named := hbs_eq
  set γ' := (γ.remove' self.runtime).removeAll' bs with hγ'_def
  set fval := Runtime.Val.fix self.runtime bs (body.runtime.subst γ') with hfval_def
  -- The constant `compile` declares for the closure, and the environment
  -- interpreting it by the closure itself.
  set fv := st.freshConst self.name .value with hfv_def
  set st₁ : State := { st with decls := st.decls.addConst fv } with hst₁_def
  set ρ₁ := ρ.updateConst .value fv.name fval with hρ₁_def
  have hfresh : fv.name ∉ st.decls.allNames := st.freshConst_fresh self.name .value
  have hst_sub₁ : st.decls.Subset st₁.decls := Signature.Subset.subset_addConst _ _
  have hρ_st₁ : Env.agreeOn st.decls ρ ρ₁ := Env.agreeOn_update_fresh_const hfresh
  have hS₁ : S.wfIn W (State.persist st₁).decls ρ₁ γg γ := Scope.wfIn_mono hS hst_sub₁
    hρ_st₁ (Signature.wf_addConst (VerifM.eval.wf heval).namesDisjoint hfresh)
  have hfv_mem : fv ∈ st₁.decls.consts := List.mem_cons_self ..
  have hfv_sort : fv.sort = .value := rfl
  have hfv_val : ρ₁.consts .value fv.name = fval := by
    rw [hρ₁_def]; simp [Env.updateConst]
  have himpl := (VerifM.eval_seq (VerifM.eval_decl (VerifM.eval_bind heval) fval)).1
  refine BIBase.Entails.trans ?_ (TinyML.ValHasType.arrow_some W fval argTys retTy s).2
  rw [hfval_def]
  refine Spec.isPrecondFor_fix (by rw [hbs_runtime]; simpa using hargNames_len)
    (by rw [hargTys_def]; simpa using hargs_len) ?_
  istart
  iintro #HT
  imodintro
  iintro #Hrec %ρ_call %vs %gs %P %hagree_call %hglen_call #Htyped #Hgtyped Hpred
  ihave %hlen_typed := TinyML.ValsHaveTypes.length_eq $$ Htyped
  have hlen_vs : bs.length = vs.length := by
    rw [hbs_runtime]; simp only [List.length_map]
    rw [hargTys_def] at hlen_typed; simp at hlen_typed
    omega
  have hsub := Runtime.Expr.subst_fix_comp body.runtime self.runtime bs γ fval vs hlen_vs
  simp only [] at hsub
  rw [hsub]
  ihave Hwand := Spec.implement_correct W argTys retTy s _ (State.persist st₁) ρ₁ vs gs P
    (TinyML.ValsHaveTypes W vs argTys -∗
      TinyML.ValsHaveTypes W gs (s.ghost.map Prod.snd) -∗
      (S.typed W γg γ ∗
        s.isPrecondFor W (TinyML.ValHasType W) argTys retTy fval) -∗
        wp W.pctx (body.runtime.subst
          ((γ.updateBinder self.runtime fval).updateAllBinder bs vs)) P)
    (by rw [hargTys_def]; simpa using hargs_len.symm) hglen_call.symm hswf henv.world hS₁.agrees
    (VerifM.eval_persist (VerifM.eval_bind himpl))
    (fun argVars ghostVars st' ρ' Q hst_sub hρ_agree hargVars_mem hargVars_sort hargVars_lookup
        hghostVars_mem hghostVars_sort hghostVars_lookup hbody_eval => by
      have hρ_st' : Env.agreeOn st₁.decls ρ₁ ρ' := by simpa using hρ_agree
      iintro ⟨Hsl, HQ⟩ Htyped'' Hgtyped''
      iapply (compileFixBody_correct _ W henv S γg γ
        self args retTy s body ih argNames hext fv fval vs gs P
        (Scope.wfIn_mono hS₁ hst_sub hρ_agree (VerifM.eval.wf hbody_eval).namesDisjoint)
        (hst_sub.consts fv hfv_mem) hfv_sort
        (by
          have h := hρ_st'.consts fv hfv_mem
          rw [hfv_sort] at h
          rw [← h]
          exact hfv_val)
        hargVars_mem hargVars_sort hargVars_lookup
        hghostVars_mem hghostVars_sort hghostVars_lookup hbody_eval)
      iframe Hsl Htyped'' Hgtyped''
      iexact HQ) $$ [Htyped Hgtyped Hpred]
  · isplitl []
    · simp [State.sl, State.persist]
      iempintro
    · iframe Htyped Hgtyped
      have hlen_call : s.allArgs.length ≤ (vs ++ gs).length := by
        rw [hargTys_def] at hlen_typed; simp [Spec.allArgs] at hlen_typed ⊢
        omega
      iapply (PredTrans.apply_agreeOn (TinyML.ValHasType W)
        (ρ := Spec.argsEnv ρ_call s.allArgs (vs ++ gs))
        (ρ' := Spec.argsEnv W.ρ_spec s.allArgs (vs ++ gs)) hswf
        (Spec.argsEnv_agreeOn (Δ := W.Δ_spec) (ρ₁ := ρ_call) (ρ₂ := W.ρ_spec)
          (Env.agreeOn_symm hagree_call) s.allArgs (vs ++ gs) hlen_call))
      iexact Hpred
  ispecialize Hwand $$ [Htyped]
  · iexact Htyped
  ispecialize Hwand $$ [Hgtyped]
  · iexact Hgtyped
  iapply Hwand
  iframe HT Hrec

theorem compileFix_correct (self : Binder) (args : List Binder)
    (retTy : TinyML.Typ) (spec : Option (Spec TinyML.Typ)) (body : Expr)
    (ih : correctExpr body) :
    correctExpr (.fix self args retTy spec body) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  cases spec with
  | none => simp only [compile] at heval; exact (VerifM.eval_fatal heval).elim
  | some s =>
  simp only [Expr.WithTypeVars.ty] at hpost
  have hval := compileFix_typed env W henv S γg γ self args retTy s body ih hS heval
  obtain ⟨reg, Θ, Δ, ls, fns, lfs, gls⟩ := env
  obtain ⟨-, -, -, rfl, rfl, -, -, -⟩ := id henv
  simp only [compile] at heval
  cases hext : extractArgNames args s.args with
  | error msg => simp only [hext] at heval; exact (VerifM.eval_fatal heval).elim
  | ok argNames =>
  cases hcheck : Spec.checkWf s W.Δ_spec with
  | error msg => simp only [hext, hcheck] at heval; exact (VerifM.eval_fatal heval).elim
  | ok u =>
  cases u
  simp only [hext, hcheck] at heval
  set bs := args.map (·.runtime) with hbs_def
  set fv := st.freshConst self.name .value with hfv_def
  set st₁ : State := { st with decls := st.decls.addConst fv } with hst₁_def
  set γ' := (γ.remove' self.runtime).removeAll' bs with hγ'_def
  set fval := Runtime.Val.fix self.runtime bs (body.runtime.subst γ') with hfval_def
  set ρ₁ := ρ.updateConst .value fv.name fval with hρ₁_def
  have hcont := (VerifM.eval_seq (VerifM.eval_decl (VerifM.eval_bind heval) fval)).2
  -- Facts about the constant standing for the closure.
  have hfresh : fv.name ∉ st.decls.allNames := st.freshConst_fresh self.name .value
  have hstwf : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
  have hρ_st₁ : Env.agreeOn st.decls ρ ρ₁ := Env.agreeOn_update_fresh_const hfresh
  have hsf_wf : (Term.const (.uninterpreted fv.name .value)).wfIn st₁.decls := by
    simpa [hst₁_def] using
      (Term.const_wfIn_addConst_of_fresh (Δ := st.decls) (c := fv) hstwf hfresh)
  have hsf_eval : (Term.const (.uninterpreted fv.name .value)).eval ρ₁ = fval := by
    simp [hρ₁_def, Term.eval, Const.eval, Env.updateConst]
  -- The closure value itself: the fresh constant denotes it.
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst_fix]
  apply PrimitiveLaws.wp_func
  refine BIBase.Entails.trans ?_
    (hpost fval ρ₁ st₁ _ (VerifM.eval_ret hcont) hsf_wf hsf_eval)
  have hsl : st.sl W ρ ⊢ st₁.sl W ρ₁ := by
    simp only [State.sl_eq, hst₁_def]
    exact (SpatialContext.interp_agreeOn W (VerifM.eval.wf heval).ownsWf hρ_st₁).1
  istart
  iintro ⟨Howns, #HT, HR⟩
  isplitl [Howns]
  · iapply hsl; iexact Howns
  · isplitl []
    · iapply hval
      iexact HT
    · iexact HR

theorem compilePrim_correct (n : String)
    (inst : List (TinyML.TyVar × TinyML.Typ)) (ty : TinyML.Typ) :
    correctExpr (.prim n inst ty) := by
  intro env W S γg γ st ρ Ψ R Φ henv _hS heval
  simp only [compile] at heval
  exact (VerifM.eval_fatal heval).elim

theorem compileRefShared_correct (e : Expr)
    (ih : correctExpr e) :
    correctExpr (.ref .shared e) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  have heval_e : (compile env S e).eval st ρ _ := VerifM.eval_bind heval
  refine PrimitiveLaws.wp_bind_ref <| ih env W S γg γ (R := R) henv hS (VerifM.eval.decls_grow ρ heval_e) ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se
  obtain ⟨_hdecls_e, _hagreeOn_e, hΨ_e⟩ := hΨ_e
  have hwf_st₁ := VerifM.eval.wf hΨ_e
  set c : Decl.Const := st₁.freshConst none .value
  have hfresh : c.name ∉ st₁.decls.allNames :=
    State.freshConst_fresh st₁ none .value
  have hwf_addConst : State.wf { st₁ with decls := st₁.decls.addConst c } :=
    State.wf_addConst _ _ hwf_st₁ hfresh
  refine PrimitiveLaws.wp_ref_inv W (ctx := st₁.owns) (ρ := ρ_e) (R := R) (ty := e.ty) ?_
  intro loc
  have hdecl_eval := VerifM.eval_bind hΨ_e
  have hret := VerifM.eval_ret (VerifM.eval_decl hdecl_eval (.loc loc))
  set ρ_e' : Env := ρ_e.updateConst .value c.name (.loc loc)
  set st₂ : State :=
    { decls := st₁.decls.addConst c, asserts := st₁.asserts, owns := st₁.owns }
  have hc_wf : (Term.const (.uninterpreted c.name .value)).wfIn st₂.decls := by
    simpa [st₂] using
      (Term.const_wfIn_addConst_of_fresh (Δ := st₁.decls) (c := c)
        hwf_st₁.namesDisjoint hfresh)
  have hval_eval : Term.eval ρ_e' (Term.const (.uninterpreted c.name .value)) = .loc loc := by
    simp [Term.eval, Const.eval, ρ_e', Env.updateConst]
  have hsl_agree : st₁.sl W ρ_e ⊢ st₂.sl W ρ_e' := by
    simp only [State.sl_eq, st₂]
    exact (SpatialContext.interp_agreeOn W hwf_st₁.ownsWf
      (Env.agreeOn_update_fresh_const (c := c) hfresh)).1
  exact (sep_mono_left hsl_agree).trans
    (hpost (.loc loc) ρ_e' st₂ (Term.const (.uninterpreted c.name .value))
      hret hc_wf hval_eval)

theorem compileRefOwned_correct (e : Expr)
    (ih : correctExpr e) :
    correctExpr (.ref .owned e) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  have heval_e : (compile env S e).eval st ρ _ := VerifM.eval_bind heval
  refine PrimitiveLaws.wp_bind_ref <| ih env W S γg γ (R := R) henv hS (VerifM.eval.decls_grow ρ heval_e) ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se
  obtain ⟨_hdecls_e, _hagreeOn_e, hΨ_e⟩ := hΨ_e
  have hdecl_eval := VerifM.eval_bind hΨ_e
  set c : Decl.Const := st₁.freshConst none .value
  set sl : Term .value := .const (.uninterpreted c.name .value)
  have hdecl := VerifM.eval_decl hdecl_eval
  have hwf_st₁ := VerifM.eval.wf hΨ_e
  have hc_fresh : c.name ∉ st₁.decls.allNames :=
    State.freshConst_fresh st₁ none .value
  have hwp :
      st₁.sl W ρ_e ∗ TinyML.ValHasType W v_e e.ty ∗ R ⊢ wp W.pctx (.ref (.val v_e)) Φ := by
    refine PrimitiveLaws.wp_ref W
      (ctx := st₁.owns) (ρ := ρ_e) (R := R) (Δ := st₁.decls)
      (vt := se) (ty := e.ty) (name := c.name)
      (newctx := SpatialContext.insert (.pointsTo sl se e.ty) st₁.owns)
      hwf_st₁.ownsWf hse_wf heval_se hc_fresh rfl ?_
    intro loc
    set ρ₂ : Env := ρ_e.updateConst .value c.name (.loc loc)
    set st₂ : State := { st₁ with decls := st₁.decls.addConst c }
    have hdecl_loc := hdecl (.loc loc)
    have hsl_wf : sl.wfIn st₂.decls := by
      simpa [sl, st₂] using
        (Term.const_wfIn_addConst_of_fresh (Δ := st₁.decls) (c := c)
          hwf_st₁.namesDisjoint hc_fresh)
    have hse_wf₂ : se.wfIn st₂.decls :=
      Term.wfIn_mono se hse_wf (Signature.Subset.subset_addConst _ _)
        (State.wf_addConst _ _ hwf_st₁ hc_fresh).namesDisjoint
    have hatom_wf : (SpatialAtom.pointsTo sl se e.ty).wfIn st₂.decls := ⟨hsl_wf, hse_wf₂⟩
    have hassumed := VerifM.eval_assumeSpatial (VerifM.eval_bind hdecl_loc) hatom_wf
    have hsl_eval : sl.eval ρ₂ = .loc loc := by
      simp [sl, ρ₂, c, Term.eval, Const.eval, Env.updateConst]
    have htyped : ∀ φ ∈ TinyML.typeConstraints (.owned e.ty) sl, φ.eval ρ₂ := by
      intro φ hφ
      simp only [TinyML.typeConstraints, List.mem_singleton] at hφ
      subst hφ
      simp [Formula.eval, hsl_eval]
    obtain ⟨st₃, hdecls₃, howns₃, _hasserts₃, hq₃⟩ :=
      VerifM.eval_assumeAll (VerifM.eval_bind hassumed)
        (fun φ hφ => TinyML.typeConstraints_wfIn hsl_wf φ hφ) htyped
    have hret := VerifM.eval_ret hq₃
    have hsl_wf₃ : sl.wfIn st₃.decls := by rw [hdecls₃]; exact hsl_wf
    have hlocTy : ⊢ TinyML.ValHasType W (.loc loc) (.owned e.ty) := by
      refine Entails.trans ?_ (TinyML.ValHasType.owned W (.loc loc) e.ty).2
      istart
      iintro _

      iexists loc
      ipureintro
      rfl
    istart
    iintro ⟨Hsl, HR⟩
    iapply (hpost (.loc loc) ρ₂ st₃ sl hret hsl_wf₃ hsl_eval)
    isplitl [Hsl]
    · simp [State.sl_eq, howns₃, SpatialContext.insert]
      rw [show ρ₂ = ρ_e.updateConst .value c.name (.loc loc) by rfl]
      iexact Hsl
    · isplitl []
      · iapply hlocTy
      · iexact HR
  exact hwp

theorem compileRef_correct (ownership : TinyML.Ownership) (e : Expr)
    (ih : correctExpr e) :
    correctExpr (.ref ownership e) := by
  cases ownership with
  | shared => exact compileRefShared_correct e ih
  | owned => exact compileRefOwned_correct e ih

theorem compileDerefShared_correct (e : Expr) (ty : TinyML.Typ)
    (href : e.ty = .ref ty)
    (ih : correctExpr e) :
    correctExpr (.deref e ty) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile, href] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  obtain ⟨_, heval⟩ := VerifM.eval_bind_expectEq heval
  have heval_e : (compile env S e).eval st ρ _ := VerifM.eval_bind heval
  refine PrimitiveLaws.wp_bind_deref <| ih env W S γg γ (R := R) henv hS (VerifM.eval.decls_grow ρ heval_e) ?_
  intro v_e ρ_e st₁ se hΨ_e _hse_wf heval_se
  obtain ⟨_hdecls_e, _hagreeOn_e, hΨ_e⟩ := hΨ_e
  have hdecl_eval := VerifM.eval_bind hΨ_e
  have hdecl := VerifM.eval_decl hdecl_eval
  set c : Decl.Const := st₁.freshConst none .value
  set sv : Term .value := .const (.uninterpreted c.name .value)
  have hc_fresh : c.name ∉ st₁.decls.allNames :=
    State.freshConst_fresh st₁ none .value
  have hc_wf : sv.wfIn (st₁.decls.addConst c) :=
    by
      simpa [sv] using
        (Term.const_wfIn_addConst_of_fresh (Δ := st₁.decls) (c := c)
          (VerifM.eval.wf hdecl_eval).namesDisjoint hc_fresh)
  rw [href]
  refine PrimitiveLaws.wp_deref_inv W (ctx := st₁.owns) (ρ := ρ_e) (R := R) (ty := ty) ?_
  intro w
  istart
  iintro ⟨Howns, #Hw, HR⟩
  have hassume_eval := VerifM.eval_bind (hdecl w)
  set ρ₂ : Env := ρ_e.updateConst .value c.name w
  have hsv_eval : sv.eval ρ₂ = w := by
    simp [sv, ρ₂, Term.eval, Const.eval, Env.updateConst]
  ihave Hcheck := TinyML.typeConstraints_hold (ty := ty) (t := sv)
    (ρ := ρ₂) (W := W) (v := w) hsv_eval $$ Hw
  ipure Hcheck
  obtain ⟨st₃, hst₃_decls, hst₃_owns, _, heval_ret⟩ := VerifM.eval_assumeAll hassume_eval
    (fun φ hφ => TinyML.typeConstraints_wfIn hc_wf φ hφ)
    (fun φ hφ => Hcheck φ hφ)
  have hsl_agree : SpatialContext.interp W ρ_e st₁.owns ⊢ st₃.sl W ρ₂ := by
    simp only [State.sl_eq, hst₃_owns]
    exact (SpatialContext.interp_agreeOn W (VerifM.eval.wf hdecl_eval).ownsWf
      (Env.agreeOn_update_fresh_const (c := c) hc_fresh)).1
  iapply (hpost w ρ₂ st₃ sv (VerifM.eval_ret heval_ret) (hst₃_decls ▸ hc_wf) hsv_eval)
  isplitl [Howns]
  · iapply hsl_agree
    iexact Howns
  · iframe Hw HR

theorem compileDerefOwned_correct (e : Expr) (ty : TinyML.Typ)
    (howned : e.ty = .owned ty)
    (ih : correctExpr e) :
    correctExpr (.deref e ty) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile, howned] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  obtain ⟨_, heval⟩ := VerifM.eval_bind_expectEq heval
  have heval_e : (compile env S e).eval st ρ _ := VerifM.eval_bind heval
  refine PrimitiveLaws.wp_bind_deref <| ih env W S γg γ (R := R) henv hS (VerifM.eval.decls_grow ρ heval_e) ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se
  obtain ⟨_hdecls_e, _hagreeOn_e, hΨ_e⟩ := hΨ_e
  have hfind_eval := VerifM.eval_bind hΨ_e
  rw [howned]
  refine VerifM.eval_findMatchForce W
    (R := TinyML.ValHasType W v_e (.owned ty) ∗ R)
    (Φ := wp W.pctx (.deref (.val v_e)) Φ) hfind_eval hse_wf ?_
  intro v st₂ hQ hdecls hv_wf
  have hassume_eval := VerifM.eval_bind hQ
  have hatom_wf : (SpatialAtom.pointsTo se v ty).wfIn st₂.decls := by
    rw [hdecls]
    exact ⟨hse_wf, hv_wf⟩
  have hassume := VerifM.eval_assumeSpatial hassume_eval hatom_wf
  have hret := VerifM.eval_ret hassume
  have hv_wf' : v.wfIn st₂.decls := by
    rw [hdecls]
    exact hv_wf
  simpa [State.sl_eq] using
    (PrimitiveLaws.wp_deref_owned W (rest := st₂.owns) (lt := se) (vt := v) (ty := ty)
      (R := R) (Q := Φ) heval_se
      (by
        simpa [State.sl_eq] using
          hpost (v.eval ρ_e) ρ_e { st₂ with owns := .pointsTo se v ty :: st₂.owns }
            v hret hv_wf' rfl))

theorem compileDeref_correct (e : Expr) (ty : TinyML.Typ)
    (ih : correctExpr e) :
    correctExpr (.deref e ty) := by
  cases hty : e.ty with
  | ref ty' =>
      by_cases heq : ty' = ty
      · have href : e.ty = .ref ty := by simpa [heq] using hty
        exact compileDerefShared_correct e ty href ih
      · intro env W S γg γ st ρ Ψ R Φ henv _hS heval _ _
        simp only [compile, hty] at heval
        obtain ⟨hannot, _⟩ := VerifM.eval_bind_expectEq heval
        exact False.elim (heq hannot)
  | owned ty' =>
      by_cases heq : ty' = ty
      · have howned : e.ty = .owned ty := by simpa [heq] using hty
        exact compileDerefOwned_correct e ty howned ih
      · intro env W S γg γ st ρ Ψ R Φ henv _hS heval _ _
        simp only [compile, hty] at heval
        obtain ⟨hannot, _⟩ := VerifM.eval_bind_expectEq heval
        exact False.elim (heq hannot)
  | prim _ | sum _ | arrow _ _ | array _ | ownedArray _ | vec _ | empty | value | tuple _ | tvar _ | named _ _ =>
      intro env W S γg γ st ρ Ψ R Φ henv _hS heval _ _
      simp only [compile, hty] at heval
      exact (VerifM.eval_fatal (VerifM.eval_bind heval)).elim

theorem compileStoreShared_correct (loc val : Expr)
    (href : loc.ty = .ref val.ty)
    (ihVal : correctExpr val) (ihLoc : correctExpr loc) :
    correctExpr (.store loc val) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile, href] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  obtain ⟨_, heval⟩ := VerifM.eval_bind_expectEq heval
  have heval_v : (compile env S val).eval st ρ _ := VerifM.eval_bind heval
  have hstart := Scope.typed_dup W S st ρ γg γ R
  refine PrimitiveLaws.wp_bind_store <| (hstart.trans <|
    ihVal env W S γg γ (R := (S.typed W γg γ ∗ (R))) henv hS (VerifM.eval.decls_grow ρ heval_v) ?_)
  intro v_v ρ_v st₁ sv hΨ_v hsv_wf heval_sv
  obtain ⟨hdecls_v, hagreeOn_v, hΨ_v⟩ := hΨ_v
  have heval_l : (compile env S loc).eval st₁ ρ_v _ := VerifM.eval_bind hΨ_v
  have hlocStart := Scope.typed_push W S st₁ ρ_v γg γ R v_v val.ty
  have hS_v := Scope.wfIn_mono hS hdecls_v hagreeOn_v (VerifM.eval.wf hΨ_v).namesDisjoint
  refine hlocStart.trans <| ihLoc env W S γg γ (R := (TinyML.ValHasType W v_v val.ty ∗ R)) henv hS_v (VerifM.eval.decls_grow ρ_v heval_l) ?_
  intro v_l ρ_l st₂ sl hΨ_l hsl_wf heval_sl
  obtain ⟨hdecls_l, hagreeOn_l, hΨ_l⟩ := hΨ_l
  obtain hret := VerifM.eval_ret hΨ_l
  have hunit_wf : (Term.const .unit).wfIn st₂.decls := by
    simp [Term.wfIn, Const.wfIn]
  have hgoal :
      st₂.sl W ρ_l ∗ TinyML.ValHasType W .unit .unit ∗ R ⊢ Φ .unit :=
    hpost .unit ρ_l st₂ _ hret hunit_wf (by simp [Term.eval])
  rw [href]
  exact PrimitiveLaws.wp_store_inv W (ctx := st₂.owns) (ρ := ρ_l) (R := R) (ty := val.ty)
    (by simpa [State.sl_eq] using hgoal)

theorem compileStoreOwned_correct (loc val : Expr)
    (howned : loc.ty = .owned val.ty)
    (ihVal : correctExpr val) (ihLoc : correctExpr loc) :
    correctExpr (.store loc val) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile, howned] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  obtain ⟨_, heval⟩ := VerifM.eval_bind_expectEq heval
  have heval_v : (compile env S val).eval st ρ _ := VerifM.eval_bind heval
  have hstart := Scope.typed_dup W S st ρ γg γ R
  refine PrimitiveLaws.wp_bind_store <| (hstart.trans <|
    ihVal env W S γg γ (R := (S.typed W γg γ ∗ (R))) henv hS (VerifM.eval.decls_grow ρ heval_v) ?_)
  intro v_v ρ_v st₁ sv hΨ_v hsv_wf heval_sv
  obtain ⟨hdecls_v, hagreeOn_v, hΨ_v⟩ := hΨ_v
  have heval_l : (compile env S loc).eval st₁ ρ_v _ := VerifM.eval_bind hΨ_v
  have hlocStart := Scope.typed_push W S st₁ ρ_v γg γ R v_v val.ty
  have hS_v := Scope.wfIn_mono hS hdecls_v hagreeOn_v (VerifM.eval.wf hΨ_v).namesDisjoint
  refine hlocStart.trans <| ihLoc env W S γg γ (R := (TinyML.ValHasType W v_v val.ty ∗ R)) henv hS_v (VerifM.eval.decls_grow ρ_v heval_l) ?_
  intro v_l ρ_l st₂ sl hΨ_l hsl_wf heval_sl
  obtain ⟨_hdecls_l, _hagreeOn_l, hΨ_l⟩ := hΨ_l
  have hfind_eval := VerifM.eval_bind hΨ_l
  have hsv_wf_l : sv.wfIn st₂.decls :=
    Term.wfIn_mono sv hsv_wf _hdecls_l (VerifM.eval.wf hΨ_l).namesDisjoint
  have heval_sv_l : sv.eval ρ_l = v_v := by
    rw [← Term.eval_agreeOn hsv_wf _hagreeOn_l]
    exact heval_sv
  rw [howned]
  refine VerifM.eval_findMatchForce W
    (R := TinyML.ValHasType W v_l (.owned val.ty) ∗ (TinyML.ValHasType W v_v val.ty ∗ R))
    (Φ := wp W.pctx (.store (.val v_l) (.val v_v)) Φ) hfind_eval hsl_wf ?_
  intro old st₃ hQ hdecls hold_wf
  have hassume_eval := VerifM.eval_bind hQ
  have hatom_wf : (SpatialAtom.pointsTo sl sv val.ty).wfIn st₃.decls := by
    rw [hdecls]
    exact ⟨hsl_wf, hsv_wf_l⟩
  have hassume := VerifM.eval_assumeSpatial hassume_eval hatom_wf
  have hret := VerifM.eval_ret hassume
  have hunit_wf : (Term.const .unit).wfIn ({ st₃ with owns := .pointsTo sl sv val.ty :: st₃.owns }).decls := by
    simp [Term.wfIn, Const.wfIn]
  simpa [State.sl_eq] using
    (PrimitiveLaws.wp_store_owned W (rest := st₃.owns) (lt := sl) (vt_old := old)
      (vt_new := sv) (ty := val.ty) (R := R) (Q := Φ) heval_sl heval_sv_l
      (by
        simpa [State.sl_eq] using
          hpost .unit ρ_l { st₃ with owns := .pointsTo sl sv val.ty :: st₃.owns }
            (Term.const .unit) hret hunit_wf (by simp [Term.eval])))

theorem compileStore_correct (loc val : Expr)
    (ihVal : correctExpr val) (ihLoc : correctExpr loc) :
    correctExpr (.store loc val) := by
  cases hty : loc.ty with
  | ref ty =>
      by_cases heq : ty = val.ty
      · have href : loc.ty = .ref val.ty := by simpa [heq] using hty
        exact compileStoreShared_correct loc val href ihVal ihLoc
      · intro env W S γg γ st ρ Ψ R Φ henv _hS heval _ _
        simp only [compile, hty] at heval
        obtain ⟨hannot, _⟩ := VerifM.eval_bind_expectEq heval
        exact False.elim (heq hannot)
  | owned ty =>
      by_cases heq : ty = val.ty
      · have howned : loc.ty = .owned val.ty := by simpa [heq] using hty
        exact compileStoreOwned_correct loc val howned ihVal ihLoc
      · intro env W S γg γ st ρ Ψ R Φ henv _hS heval _ _
        simp only [compile, hty] at heval
        obtain ⟨hannot, _⟩ := VerifM.eval_bind_expectEq heval
        exact False.elim (heq hannot)
  | prim _ | sum _ | arrow _ _ | array _ | ownedArray _ | vec _ | empty | value | tuple _ | tvar _ | named _ _ =>
      intro env W S γg γ st ρ Ψ R Φ henv _hS heval _ _
      simp only [compile, hty] at heval
      exact (VerifM.eval_fatal (VerifM.eval_bind heval)).elim

/-- Array allocation correctness: after evaluating the initial value and the
length, the shared branch allocates behind the array invariant while the
owned branch acquires a fresh owned-array atom. -/
theorem compileArrayMake_correct (ownership : TinyML.Ownership) (len init : Expr)
    (ihLen : correctExpr len) (ihInit : correctExpr init) :
    correctExpr (.arrayMake ownership len init) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  obtain ⟨hlenty, heval⟩ := VerifM.eval_bind_expectEq heval
  have heval_init : (compile env S init).eval st ρ _ := VerifM.eval_bind heval
  refine PrimitiveLaws.wp_bind_arrayMake <| ?_
  -- Evaluate `init`.
  have hstart := Scope.typed_dup W S st ρ γg γ R
  refine hstart.trans <| ihInit env W S γg γ (R := (S.typed W γg γ ∗ (R))) henv hS (VerifM.eval.decls_grow ρ heval_init) ?_
  intro v_init ρ_init st₁ s_init hΨ_init hsinit_wf heval_sinit
  obtain ⟨hdecls_init, hagreeOn_init, hΨ_init⟩ := hΨ_init
  have heval_len : (compile env S len).eval st₁ ρ_init _ := VerifM.eval_bind hΨ_init
  have hlenStart := Scope.typed_push W S st₁ ρ_init γg γ R v_init init.ty
  have hS_init := Scope.wfIn_mono hS hdecls_init hagreeOn_init (VerifM.eval.wf hΨ_init).namesDisjoint
  -- Evaluate `len`, carrying `init`'s typing.
  refine hlenStart.trans <| ihLen env W S γg γ (R := (TinyML.ValHasType W v_init init.ty ∗ R)) henv hS_init (VerifM.eval.decls_grow ρ_init heval_len) ?_
  intro v_len ρ_len st₂ slen hΨ_len hslen_wf heval_slen
  obtain ⟨hdecls_len, hagreeOn_len, hΨ_len⟩ := hΨ_len
  -- Discharge the nonnegative-length obligation.
  set φ : Formula := .binpred .le (.const (.i 0)) (.unop .toInt slen)
  have hwf_φ : φ.wfIn st₂.decls := by
    simpa [φ, Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, BinPred.wfIn] using hslen_wf
  obtain ⟨hφ, hcont⟩ := VerifM.eval_assert (VerifM.eval_bind hΨ_len) hwf_φ
  -- The fresh constant standing for the allocated array.
  have hdecl_eval := VerifM.eval_bind hcont
  have hdecl := VerifM.eval_decl hdecl_eval
  have hst₂_wf : st₂.wf := VerifM.eval.wf hdecl_eval
  set c : Decl.Const := st₂.freshConst none .value
  set sa : Term .value := .const (.uninterpreted c.name .value)
  have hc_fresh : c.name ∉ st₂.decls.allNames := State.freshConst_fresh st₂ none .value
  have hc_wf : sa.wfIn (st₂.decls.addConst c) := by
    simpa [sa] using Term.const_wfIn_addConst_of_fresh (Δ := st₂.decls) (c := c)
      hst₂_wf.namesDisjoint hc_fresh
  rw [hlenty]
  istart
  iintro ⟨Howns, Hlen, #Hinit, HR⟩
  ihave Hlen' := (TinyML.ValHasType.int W v_len).1 $$ Hlen
  icases Hlen' with ⟨%n, %hv_len⟩
  have hn : (0 : Int) ≤ n := by
    simpa [φ, Formula.eval, BinPred.eval, Term.eval, Const.eval, UnOp.eval,
      heval_slen, hv_len] using hφ
  cases ownership with
  | shared =>
    simp only [Expr.WithTypeVars.ty] at hpost
    iapply (PrimitiveLaws.wp_arrayMake_inv (vlen := v_len) (init := v_init) (n := n)
      (I := fun w => TinyML.ValHasType W w init.ty) (Q := Φ) hv_len hn)
    isplitl []
    · imodintro
      iexact Hinit
    · iintro %l #Hinv_l
      -- Run the verifier's assume/assumeAll, instantiating the result with the
      -- freshly allocated array value `.array n.toNat l`.
      have hbody := hdecl (.array n.toNat l)
      have hassume_eval := VerifM.eval_bind hbody
      set ρ' : Env := ρ_len.updateConst .value c.name (.array n.toNat l)
      set st_c : State := { st₂ with decls := st₂.decls.addConst c } with hst_c_def
      have hsa_eval : sa.eval ρ' = .array n.toNat l := by
        simp [sa, ρ', Term.eval, Const.eval, Env.updateConst]
      have hslen_eval' : slen.eval ρ' = .int n :=
        (Term.eval_agreeOn hslen_wf
          (Env.agreeOn_update_fresh_const (c := c)
            (u := Runtime.Val.array n.toNat l) hc_fresh)).symm.trans (heval_slen.trans hv_len)
      -- The length equation assumed after allocation.
      have hstc_wf : (st₂.decls.addConst c).wf :=
        Signature.wf_addConst hst₂_wf.namesDisjoint hc_fresh
      have hslen_wf_c : slen.wfIn st_c.decls :=
        Term.wfIn_mono slen hslen_wf (Signature.Subset.subset_addConst _ _) hstc_wf
      have heqφ_wf :
          (CtxItem.pure (Formula.eq Srt.int (.unop .arrayLen sa) (.unop .toInt slen))).wfIn st_c.decls := by
        refine ⟨⟨trivial, hc_wf⟩, ⟨trivial, hslen_wf_c⟩⟩
      have heqφ_hold :
          (Formula.eq Srt.int (.unop .arrayLen sa) (.unop .toInt slen)).eval ρ' := by
        simp [Formula.eval, Term.eval, UnOp.eval, hsa_eval, hslen_eval']
        omega
      have hassumeAll := VerifM.eval_assume hassume_eval heqφ_wf heqφ_hold
      have hassumeAll_eval := VerifM.eval_bind hassumeAll
      ihave HarrTy := (TinyML.ValHasType.array W (.array n.toNat l) init.ty).2 $$ [Hinv_l]
      · iexists n.toNat, l
        isplitr
        · ipureintro; rfl
        · iexact Hinv_l
      ihave %htyped_formulas := (TinyML.typeConstraints_hold
        (ty := TinyML.Typ.array init.ty) (t := sa) (ρ := ρ') (W := W)
        (v := .array n.toNat l) hsa_eval) $$ HarrTy
      obtain ⟨st_final, hst_final_decls, hst_final_owns, _, heval_ret⟩ :=
        VerifM.eval_assumeAll hassumeAll_eval
          (fun ψ hψ => TinyML.typeConstraints_wfIn hc_wf ψ hψ)
          (fun ψ hψ => htyped_formulas ψ hψ)
      have hΨ_ret := VerifM.eval_ret heval_ret
      have hsa_wf : sa.wfIn st_final.decls := hst_final_decls ▸ hc_wf
      have hsl_agree : st₂.sl W ρ_len ⊢ st_final.sl W ρ' := by
        simp only [State.sl_eq, hst_final_owns, State.addItem, hst_c_def]
        exact (SpatialContext.interp_agreeOn W hst₂_wf.ownsWf
          (Env.agreeOn_update_fresh_const (c := c) hc_fresh)).1
      iapply (hpost (.array n.toNat l) ρ' st_final sa hΨ_ret hsa_wf hsa_eval)
      isplitl [Howns]
      · iapply hsl_agree
        iexact Howns
      · isplitl [Hinv_l]
        · iapply (TinyML.ValHasType.array W (.array n.toNat l) init.ty).2
          iexists n.toNat, l
          isplitr
          · ipureintro; rfl
          · iexact Hinv_l
        · iexact HR
  | owned =>
    simp only [Expr.WithTypeVars.ty] at hpost
    iapply (PrimitiveLaws.wp_arrayMake (vlen := v_len) (init := v_init) (n := n)
      (Q := Φ) hv_len hn)
    iintro %l Hpt
    have hbody := hdecl (.array n.toNat l)
    set ρ' : Env := ρ_len.updateConst .value c.name (.array n.toNat l)
    set st_c : State := { st₂ with decls := st₂.decls.addConst c }
    have hsa_eval : sa.eval ρ' = .array n.toNat l := by
      simp [sa, ρ', Term.eval, Const.eval, Env.updateConst]
    have hslen_eval' : slen.eval ρ' = .int n :=
      (Term.eval_agreeOn hslen_wf
        (Env.agreeOn_update_fresh_const (c := c) (u := Runtime.Val.array n.toNat l) hc_fresh)).symm.trans
        (heval_slen.trans hv_len)
    have hsinit_wf₂ : s_init.wfIn st₂.decls :=
      Term.wfIn_mono s_init hsinit_wf hdecls_len hst₂_wf.namesDisjoint
    have hsinit_eval_len : s_init.eval ρ_len = v_init := by
      rw [Term.eval_agreeOn hsinit_wf (Env.agreeOn_symm hagreeOn_len)]
      exact heval_sinit
    have hsinit_eval' : s_init.eval ρ' = v_init :=
      (Term.eval_agreeOn hsinit_wf₂
        (Env.agreeOn_update_fresh_const (c := c) (u := Runtime.Val.array n.toNat l) hc_fresh)).symm.trans
        hsinit_eval_len
    have hstc_wf : (st₂.decls.addConst c).wf := Signature.wf_addConst hst₂_wf.namesDisjoint hc_fresh
    have hslen_wf_c := Term.wfIn_mono slen hslen_wf (Signature.Subset.subset_addConst _ _) hstc_wf
    have hsinit_wf_c := Term.wfIn_mono s_init hsinit_wf₂ (Signature.Subset.subset_addConst _ _) hstc_wf
    have heq_wf : (CtxItem.pure
        (.eq .int (.unop .arrayLen sa) (.unop .toInt slen))).wfIn st_c.decls :=
      ⟨⟨trivial, hc_wf⟩, ⟨trivial, hslen_wf_c⟩⟩
    have heq_hold : Formula.eval ρ'
        (.eq .int (.unop .arrayLen sa) (.unop .toInt slen)) := by
      simp [Formula.eval, Term.eval, UnOp.eval, hsa_eval, hslen_eval']
      omega
    have hassume := VerifM.eval_assume (VerifM.eval_bind hbody) heq_wf heq_hold
    let contents : Term .value := .unop .ofVec
      (.binop .vecMake (.unop .toInt slen) s_init)
    have hcontents_wf : contents.wfIn st_c.decls :=
      ⟨trivial, ⟨trivial, ⟨trivial, hslen_wf_c⟩, hsinit_wf_c⟩⟩
    have hatom_wf : (SpatialAtom.arrayPointsTo sa contents init.ty).wfIn st_c.decls :=
      ⟨hc_wf, hcontents_wf⟩
    have hcontents_eval : contents.eval ρ' = .vec (List.replicate n.toNat v_init) := by
      simp [contents, Term.eval, UnOp.eval, BinOp.eval, hslen_eval', hsinit_eval', hn]
    ihave #HvecTy : iprop(TinyML.ValHasType W (.vec (List.replicate n.toNat v_init)) (.vec init.ty)) $$ [Hinit]
    · iapply TinyML.ValHasType.vec_replicate
      iexact Hinit
    ihave %helements := TinyML.elementConstraints_hold (ty := init.ty) hcontents_eval $$ HvecTy
    -- Acquire the owned-array atom; all snapshot facts hold by construction.
    have hfacts : ∀ ψ ∈ (CtxItem.spatial (.arrayPointsTo sa contents init.ty)).facts,
        ψ.eval ρ' := by
      intro ψ hψ
      simp only [CtxItem.facts, SpatialAtom.facts, List.mem_cons] at hψ
      rcases hψ with rfl | hψ
      · simp [Formula.eval, Term.eval, UnOp.eval, hcontents_eval, hsa_eval]
      · exact helements ψ hψ
    obtain ⟨st_a, hdecls_a, howns_a, hq_a⟩ :=
      VerifM.eval_acquire (VerifM.eval_bind hassume) hatom_wf trivial hfacts
    have hArrTy : ⊢ TinyML.ValHasType W (.array n.toNat l) (.ownedArray init.ty) := by
      iapply (TinyML.ValHasType.ownedArray W _ _).2
      iexists n.toNat, l
      ipureintro; rfl
    ihave HarrTy := hArrTy
    ihave %htyped := TinyML.typeConstraints_hold (ty := .ownedArray init.ty) (t := sa)
      (ρ := ρ') (W := W) hsa_eval $$ HarrTy
    obtain ⟨st_final, hdecls_final, howns_final, _, heval_ret⟩ :=
      VerifM.eval_assumeAll (VerifM.eval_bind hq_a)
        (fun ψ hψ => by rw [hdecls_a]; exact TinyML.typeConstraints_wfIn hc_wf ψ hψ)
        (fun ψ hψ => htyped ψ hψ)
    have hret := VerifM.eval_ret heval_ret
    have hsa_wf_final : sa.wfIn st_final.decls := by
      rw [hdecls_final, hdecls_a]; exact hc_wf
    have hsl_agree : SpatialContext.interp W ρ_len st₂.owns ⊢
        SpatialContext.interp W ρ' st₂.owns := by
      rw [show ρ' = ρ_len.updateConst .value c.name (.array n.toNat l) by rfl]
      exact (SpatialContext.interp_agreeOn W hst₂_wf.ownsWf
        (Env.agreeOn_update_fresh_const (ρ := ρ_len) (c := c)
          (u := Runtime.Val.array n.toNat l) hc_fresh)).1
    iapply (hpost (.array n.toNat l) ρ' st_final sa hret hsa_wf_final hsa_eval)
    isplitl [Hpt Howns]
    · simp only [State.sl_eq, howns_final, howns_a, State.addItem, st_c,
        SpatialContext.interp]
      isplitl [Hpt]
      · iapply (SpatialAtom.interp_arrayPointsTo W (by simpa using hsa_eval) hcontents_eval).2
        iframe Hpt HvecTy
      · iapply hsl_agree
        iexact Howns
    · iframe HarrTy HR

theorem compileArrayLen_correct (arr : Expr)
    (ihArr : correctExpr arr) :
    correctExpr (.arrayLen arr) := by
  cases hty : arr.ty with
  | array elem =>
      intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
      unfold Expr.WithTypeVars.runtime
      simp only [Runtime.Expr.subst]
      simp only [compile, hty] at heval
      have heval_arr : (compile env S arr).eval st ρ _ :=
        VerifM.eval_bind heval
      refine PrimitiveLaws.wp_bind_arrayLen <| ihArr env W S γg γ (R := R) henv hS (VerifM.eval.decls_grow ρ heval_arr) ?_
      intro v_arr ρ_arr st₁ sa hΨ_arr hsa_wf heval_sa
      obtain ⟨_, _, hΨ_arr⟩ := hΨ_arr
      obtain hret := VerifM.eval_ret hΨ_arr
      set t : Term .value := .unop .ofInt (.unop .arrayLen sa)
      have ht_wf : t.wfIn st₁.decls := by
        exact ⟨trivial, ⟨trivial, hsa_wf⟩⟩
      have hwp :
          st₁.sl W ρ_arr ∗ TinyML.ValHasType W v_arr arr.ty ∗ R ⊢
            wp W.pctx (.arrayLen (.val v_arr)) Φ := by
        rw [hty]
        istart
        iintro ⟨Howns, Harr, HR⟩
        ihave Harr' := (TinyML.ValHasType.array W v_arr elem).1 $$ Harr
        icases Harr' with ⟨%len, %loc, %hv_arr, _⟩
        have ht_eval : t.eval ρ_arr = Runtime.Val.int len := by
          simp [t, Term.eval, UnOp.eval, heval_sa, hv_arr]
        have hgoal :
            st₁.sl W ρ_arr ∗ TinyML.ValHasType W (.int len) TinyML.Typ.int ∗ R ⊢
              Φ (.int len) :=
          by
            simpa [Expr.WithTypeVars.ty] using hpost (.int len) ρ_arr st₁ t hret ht_wf ht_eval
        iapply (PrimitiveLaws.wp_arrayLen
          (R := st₁.sl W ρ_arr ∗ TinyML.ValHasType W (.int len) TinyML.Typ.int ∗ R)
          (Q := Φ) (v := v_arr) (len := len) (l := loc) hv_arr hgoal)
        isplitl [Howns]
        · iexact Howns
        · isplitl []
          · iapply (TinyML.ValHasType.int_intro W)
          · iexact HR
      exact hwp
  | ownedArray elem =>
      intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
      unfold Expr.WithTypeVars.runtime
      simp only [Runtime.Expr.subst]
      simp only [compile, hty] at heval
      have heval_arr : (compile env S arr).eval st ρ _ :=
        VerifM.eval_bind heval
      refine PrimitiveLaws.wp_bind_arrayLen <| ihArr env W S γg γ (R := R) henv hS (VerifM.eval.decls_grow ρ heval_arr) ?_
      intro v_arr ρ_arr st₁ sa hΨ_arr hsa_wf heval_sa
      obtain ⟨_, _, hΨ_arr⟩ := hΨ_arr
      obtain hret := VerifM.eval_ret hΨ_arr
      set t : Term .value := .unop .ofInt (.unop .arrayLen sa)
      have ht_wf : t.wfIn st₁.decls := ⟨trivial, ⟨trivial, hsa_wf⟩⟩
      rw [hty]
      istart
      iintro ⟨Howns, Harr, HR⟩
      ihave Harr' := (TinyML.ValHasType.ownedArray W v_arr elem).1 $$ Harr
      icases Harr' with ⟨%len, %loc, %hv_arr⟩
      have ht_eval : t.eval ρ_arr = Runtime.Val.int len := by
        simp [t, Term.eval, UnOp.eval, heval_sa, hv_arr]
      have hgoal :
          st₁.sl W ρ_arr ∗ TinyML.ValHasType W (.int len) TinyML.Typ.int ∗ R ⊢
            Φ (.int len) := by
        simpa [Expr.WithTypeVars.ty] using hpost (.int len) ρ_arr st₁ t hret ht_wf ht_eval
      iapply (PrimitiveLaws.wp_arrayLen
        (R := st₁.sl W ρ_arr ∗ TinyML.ValHasType W (.int len) TinyML.Typ.int ∗ R)
        (Q := Φ) (v := v_arr) (len := len) (l := loc) hv_arr hgoal)
      isplitl [Howns]
      · iexact Howns
      · isplitl []
        · iapply (TinyML.ValHasType.int_intro W)
        · iexact HR
  | prim _ | sum _ | arrow _ _ | ref _ | vec _ | owned _ | empty | value | tuple _ | tvar _
  | named _ _ =>
      intro env W S γg γ st ρ Ψ R Φ henv _hS heval _ _ _ _
      simp only [compile, hty] at heval
      exact (VerifM.eval_fatal heval).elim

theorem compileArrayGet_correct (arr idx : Expr) (ty : TinyML.Typ)
    (ihArr : correctExpr arr) (ihIdx : correctExpr idx) :
    correctExpr (.arrayGet arr idx ty) := by
  cases hty : arr.ty with
  | array elemTy =>
    intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
    unfold Expr.WithTypeVars.runtime
    simp only [Runtime.Expr.subst]
    simp only [compile, hty] at heval
    simp only [Expr.WithTypeVars.ty] at hpost
    replace heval := VerifM.eval_ret (VerifM.eval_bind heval)
    obtain ⟨helem, heval⟩ := VerifM.eval_bind_expectEq heval
    obtain ⟨hidxty, heval⟩ := VerifM.eval_bind_expectEq heval
    subst helem
    have heval_idx : (compile env S idx).eval st ρ _ := VerifM.eval_bind heval
    refine PrimitiveLaws.wp_bind_arrayGet <| ?_
    have hstart := Scope.typed_dup W S st ρ γg γ R
    refine hstart.trans <| ihIdx env W S γg γ (R := (S.typed W γg γ ∗ (R))) henv hS (VerifM.eval.decls_grow ρ heval_idx) ?_
    intro v_idx ρ_idx st₁ si hΨ_idx hsi_wf heval_si
    obtain ⟨hdecls_idx, hagreeOn_idx, hΨ_idx⟩ := hΨ_idx
    have heval_arr : (compile env S arr).eval st₁ ρ_idx _ := VerifM.eval_bind hΨ_idx
    have harrStart := Scope.typed_push W S st₁ ρ_idx γg γ R v_idx idx.ty
    have hS_idx := Scope.wfIn_mono hS hdecls_idx hagreeOn_idx (VerifM.eval.wf hΨ_idx).namesDisjoint
    refine harrStart.trans <| ihArr env W S γg γ (R := (TinyML.ValHasType W v_idx idx.ty ∗ R)) henv hS_idx (VerifM.eval.decls_grow ρ_idx heval_arr) ?_

    intro v_arr ρ_arr st₂ sa hΨ_arr hsa_wf heval_sa
    obtain ⟨hdecls_arr, hagreeOn_arr, hΨ_arr⟩ := hΨ_arr
    have hsi_wf₂ : si.wfIn st₂.decls :=
      Term.wfIn_mono si hsi_wf hdecls_arr (VerifM.eval.wf hΨ_arr).namesDisjoint
    have hsi_ρ_arr : si.eval ρ_arr = v_idx := by
      rw [Term.eval_agreeOn hsi_wf (Env.agreeOn_symm hagreeOn_arr)]; exact heval_si
    obtain ⟨hi, hlt, hcont2⟩ := VerifM.eval_assertBounds (VerifM.eval_bind hΨ_arr) hsi_wf₂ hsa_wf
    have hdecl_eval := VerifM.eval_bind hcont2
    have hdecl := VerifM.eval_decl hdecl_eval
    set c : Decl.Const := st₂.freshConst none .value
    set sv : Term .value := .const (.uninterpreted c.name .value)
    have hc_fresh : c.name ∉ st₂.decls.allNames := State.freshConst_fresh st₂ none .value
    have hc_wf : sv.wfIn (st₂.decls.addConst c) := by
      simpa [sv] using
        (Term.const_wfIn_addConst_of_fresh (Δ := st₂.decls) (c := c)
          (VerifM.eval.wf hdecl_eval).namesDisjoint hc_fresh)
    have hwp :
        st₂.sl W ρ_arr ∗ TinyML.ValHasType W v_arr arr.ty ∗
          (TinyML.ValHasType W v_idx idx.ty ∗ R) ⊢
          wp W.pctx (.arrayGet (.val v_arr) (.val v_idx)) Φ := by
      rw [hty, hidxty]
      simpa [State.sl_eq] using
        (PrimitiveLaws.wp_arrayGet_inv (W := W)
          (ctx := st₂.owns) (ρ := ρ_arr) (arr := sa) (idx := si)
          (elemTy := elemTy) (varr := v_arr) (vidx := v_idx) (Q := Φ) (R := R)
          heval_sa hsi_ρ_arr hi hlt (by
            intro w
            istart
            iintro ⟨Howns, #Hw, HR⟩
            have hdecl_w := hdecl w
            have hassume_eval := VerifM.eval_bind hdecl_w
            set ρ₂ : Env := ρ_arr.updateConst .value c.name w
            set st_c : State := { st₂ with decls := st₂.decls.addConst c }
            have hsv_eval : sv.eval ρ₂ = w := by
              simp [sv, ρ₂, Term.eval, Const.eval, Env.updateConst]
            ihave Hcheck := TinyML.typeConstraints_hold (ty := elemTy) (t := sv)
              (ρ := ρ₂) (W := W) (v := w) hsv_eval $$ Hw
            ipure Hcheck
            obtain ⟨st₃, hst₃_decls, hst₃_owns, _, heval_ret⟩ := VerifM.eval_assumeAll hassume_eval
              (fun φ hφ => TinyML.typeConstraints_wfIn hc_wf φ hφ)
              (fun φ hφ => Hcheck φ hφ)
            have hΨ_ret := VerifM.eval_ret heval_ret
            have hsv_wf : sv.wfIn st₃.decls := hst₃_decls ▸ hc_wf
            have hsl_agree : st₂.sl W ρ_arr ⊢ st₃.sl W ρ₂ := by
              simp [State.sl_eq, st_c, hst₃_owns]
              exact (SpatialContext.interp_agreeOn W (VerifM.eval.wf hdecl_eval).ownsWf
                (Env.agreeOn_update_fresh_const (c := c) hc_fresh)).1
            have hsl_agree' : SpatialContext.interp W ρ_arr st₂.owns ⊢ st₃.sl W ρ₂ := by
              simpa [State.sl_eq] using hsl_agree
            iapply (hpost w ρ₂ st₃ sv hΨ_ret hsv_wf hsv_eval)
            isplitl [Howns]
            · iapply hsl_agree'
              iexact Howns
            · iframe Hw HR))
    exact hwp
  | ownedArray elemTy =>
    intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
    unfold Expr.WithTypeVars.runtime
    simp only [Runtime.Expr.subst]
    simp only [compile, hty] at heval
    simp only [Expr.WithTypeVars.ty] at hpost
    replace heval := VerifM.eval_ret (VerifM.eval_bind heval)
    obtain ⟨helem, heval⟩ := VerifM.eval_bind_expectEq heval
    obtain ⟨hidxty, heval⟩ := VerifM.eval_bind_expectEq heval
    subst ty
    have heval_idx : (compile env S idx).eval st ρ _ := VerifM.eval_bind heval
    refine PrimitiveLaws.wp_bind_arrayGet <| ?_
    have hstart := Scope.typed_dup W S st ρ γg γ R
    refine hstart.trans <| ihIdx env W S γg γ (R := (S.typed W γg γ ∗ (R))) henv hS (VerifM.eval.decls_grow ρ heval_idx) ?_
    intro v_idx ρ_idx st₁ si hΨ_idx hsi_wf heval_si
    obtain ⟨hdecls_idx, hagreeOn_idx, hΨ_idx⟩ := hΨ_idx
    have heval_arr : (compile env S arr).eval st₁ ρ_idx _ := VerifM.eval_bind hΨ_idx
    have harrStart := Scope.typed_push W S st₁ ρ_idx γg γ R v_idx idx.ty
    have hS_idx := Scope.wfIn_mono hS hdecls_idx hagreeOn_idx (VerifM.eval.wf hΨ_idx).namesDisjoint
    refine harrStart.trans <| ihArr env W S γg γ (R := (TinyML.ValHasType W v_idx idx.ty ∗ R)) henv hS_idx (VerifM.eval.decls_grow ρ_idx heval_arr) ?_
    intro v_arr ρ_arr st₂ sa hΨ_arr hsa_wf heval_sa
    obtain ⟨hdecls_arr, hagreeOn_arr, hΨ_arr⟩ := hΨ_arr
    have hsi_wf₂ := Term.wfIn_mono si hsi_wf hdecls_arr (VerifM.eval.wf hΨ_arr).namesDisjoint
    have hsi_eval : si.eval ρ_arr = v_idx := by
      rw [Term.eval_agreeOn hsi_wf (Env.agreeOn_symm hagreeOn_arr)]; exact heval_si
    obtain ⟨hi, hlt, hcont2⟩ := VerifM.eval_assertBounds (VerifM.eval_bind hΨ_arr) hsi_wf₂ hsa_wf
    have hfind := VerifM.eval_bind hcont2
    rw [hty, hidxty]
    refine VerifM.eval_findMatchForce W
      (R := TinyML.ValHasType W v_arr (.ownedArray elemTy) ∗ TinyML.ValHasType W v_idx .int ∗ R)
      (Φ := wp W.pctx (.arrayGet (.val v_arr) (.val v_idx)) Φ) hfind hsa_wf ?_
    intro contents st₃ hQ hdecls hcontents_wf
    have hatom_wf : (SpatialAtom.arrayPointsTo sa contents elemTy).wfIn st₃.decls := by
      rw [hdecls]; exact ⟨hsa_wf, hcontents_wf⟩
    let result : Term .value := .binop .vecGet (.unop .toVec contents) (.unop .toInt si)
    simpa [State.sl_eq] using
      (PrimitiveLaws.wp_arrayGet_owned (W := W)
        (rest := st₃.owns) (arr := sa) (contents := contents) (idx := si)
        (result := result) (elemTy := elemTy) (varr := v_arr) (vidx := v_idx)
        (Q := Φ) (R := R) heval_sa hsi_eval hi hlt rfl (by
          -- Acquire the restored atom, then conclude with the postcondition.
          have hstep := VerifM.eval_acquireSpatial W
            (R := TinyML.ValHasType W (Term.eval ρ_arr result) elemTy ∗ R)
            (Φ := Φ (Term.eval ρ_arr result)) (VerifM.eval_bind hQ) hatom_wf
            (fun st₄ hq₄ hdecls₄ _howns₄ =>
              hpost (Term.eval ρ_arr result) ρ_arr st₄ result (VerifM.eval_ret hq₄)
                (by rw [hdecls₄, hdecls]
                    exact ⟨trivial, ⟨trivial, hcontents_wf⟩, ⟨trivial, hsi_wf₂⟩⟩)
                rfl)
          simp only [SpatialContext.interp_insert]
          istart
          iintro ⟨⟨Hatom, Howns⟩, HresTy, HR⟩
          iapply hstep
          isplitl [Hatom]
          · iexact Hatom
          · isplitl [Howns]
            · simp only [State.sl_eq]
              iexact Howns
            · iframe HresTy HR))
  | prim _ | sum _ | arrow _ _ | ref _ | vec _ | owned _ | empty | value | tuple _ | tvar _
  | named _ _ =>
      intro env W S γg γ st ρ Ψ R Φ henv _hS heval _ _ _ _
      simp only [compile, hty] at heval
      exact (VerifM.eval_fatal (VerifM.eval_bind heval)).elim

theorem compileArraySet_correct (arr idx val : Expr)
    (ihArr : correctExpr arr) (ihIdx : correctExpr idx) (ihVal : correctExpr val) :
    correctExpr (.arraySet arr idx val) := by
  cases hty : arr.ty with
  | array elemTy =>
    intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
    unfold Expr.WithTypeVars.runtime
    simp only [Runtime.Expr.subst]
    simp only [compile, hty] at heval
    simp only [Expr.WithTypeVars.ty] at hpost
    replace heval := VerifM.eval_ret (VerifM.eval_bind heval)
    obtain ⟨helemTy, heval⟩ := VerifM.eval_bind_expectEq heval
    obtain ⟨hidxty, heval⟩ := VerifM.eval_bind_expectEq heval
    have heval_val : (compile env S val).eval st ρ _ := VerifM.eval_bind heval
    refine PrimitiveLaws.wp_bind_arraySet <| ?_
    -- Evaluate `val`.
    have hstart := Scope.typed_dup W S st ρ γg γ R
    refine hstart.trans <| ihVal env W S γg γ (R := (S.typed W γg γ ∗ (R))) henv hS (VerifM.eval.decls_grow ρ heval_val) ?_
    intro v_val ρ_val st₁ sv hΨ_val hsv_wf heval_sv
    obtain ⟨hdecls_val, hagreeOn_val, hΨ_val⟩ := hΨ_val
    have heval_idx : (compile env S idx).eval st₁ ρ_val _ := VerifM.eval_bind hΨ_val
    have hS_val := Scope.wfIn_mono hS hdecls_val hagreeOn_val (VerifM.eval.wf hΨ_val).namesDisjoint
    -- Evaluate `idx`, re-exposing the spec context and carrying `val`'s typing.
    have hstepB :=
      (Scope.typed_push W S st₁ ρ_val γg γ R v_val val.ty).trans
        (Scope.typed_dup W S st₁ ρ_val γg γ (TinyML.ValHasType W v_val val.ty ∗ R))
    refine hstepB.trans <| ihIdx env W S γg γ (R := (S.typed W γg γ ∗ ((TinyML.ValHasType W v_val val.ty ∗ R)))) henv hS_val (VerifM.eval.decls_grow ρ_val heval_idx) ?_

    intro v_idx ρ_idx st₂ si hΨ_idx hsi_wf heval_si
    obtain ⟨hdecls_idx, hagreeOn_idx, hΨ_idx⟩ := hΨ_idx
    have heval_arr : (compile env S arr).eval st₂ ρ_idx _ := VerifM.eval_bind hΨ_idx
    have hS_idx := Scope.wfIn_mono hS_val hdecls_idx hagreeOn_idx (VerifM.eval.wf hΨ_idx).namesDisjoint
    -- Evaluate `arr`, carrying both `idx`'s and `val`'s typings.
    have hstepC := Scope.typed_push W S st₂ ρ_idx γg γ
      (TinyML.ValHasType W v_val val.ty ∗ R) v_idx idx.ty
    refine hstepC.trans <| ihArr env W S γg γ (R := (TinyML.ValHasType W v_idx idx.ty ∗ (TinyML.ValHasType W v_val val.ty ∗ R))) henv hS_idx (VerifM.eval.decls_grow ρ_idx heval_arr) ?_
    intro v_arr ρ_arr st₃ sa hΨ_arr hsa_wf heval_sa
    obtain ⟨hdecls_arr, hagreeOn_arr, hΨ_arr⟩ := hΨ_arr
    have hsi_wf₃ : si.wfIn st₃.decls :=
      Term.wfIn_mono si hsi_wf hdecls_arr (VerifM.eval.wf hΨ_arr).namesDisjoint
    have hsi_ρ_arr : si.eval ρ_arr = v_idx := by
      rw [Term.eval_agreeOn hsi_wf (Env.agreeOn_symm hagreeOn_arr)]; exact heval_si
    -- Discharge the two bounds obligations.
    obtain ⟨hi, hlt, hcont2⟩ := VerifM.eval_assertBounds (VerifM.eval_bind hΨ_arr) hsi_wf₃ hsa_wf
    have hret := VerifM.eval_ret (VerifM.eval_ret (VerifM.eval_bind hcont2))
    have hunit_wf : (Term.const .unit).wfIn st₃.decls := by simp [Term.wfIn, Const.wfIn]
    have hgoal :
        st₃.sl W ρ_arr ∗ TinyML.ValHasType W .unit .unit ∗ R ⊢ Φ .unit :=
      hpost .unit ρ_arr st₃ _ hret hunit_wf (by simp [Term.eval])
    have hwp :
        st₃.sl W ρ_arr ∗ TinyML.ValHasType W v_arr arr.ty ∗
          (TinyML.ValHasType W v_idx idx.ty ∗ (TinyML.ValHasType W v_val val.ty ∗ R)) ⊢
          wp W.pctx (.arraySet (.val v_arr) (.val v_idx) (.val v_val)) Φ := by
      rw [hty, hidxty, ← helemTy]
      simpa [State.sl_eq] using
        (PrimitiveLaws.wp_arraySet_inv (W := W)
          (ctx := st₃.owns) (ρ := ρ_arr) (arr := sa) (idx := si)
          (elemTy := elemTy) (varr := v_arr) (vidx := v_idx) (val := v_val)
          (Q := Φ) (R := R) heval_sa hsi_ρ_arr hi hlt (by
            have hgoal' :
                SpatialContext.interp W ρ_arr st₃.owns ∗
                  TinyML.ValHasType W .unit .unit ∗ R ⊢ Φ .unit := by
              simpa [State.sl_eq] using hgoal
            istart
            iintro ⟨Howns, _, HR⟩
            iapply hgoal'
            isplitl [Howns]
            · iexact Howns
            · isplitl []
              · iapply (TinyML.ValHasType.unit_intro W)
              · iexact HR))
    exact hwp
  | ownedArray elemTy =>
    intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
    unfold Expr.WithTypeVars.runtime
    simp only [Runtime.Expr.subst]
    simp only [compile, hty] at heval
    simp only [Expr.WithTypeVars.ty] at hpost
    replace heval := VerifM.eval_ret (VerifM.eval_bind heval)
    obtain ⟨helemTy, heval⟩ := VerifM.eval_bind_expectEq heval
    obtain ⟨hidxty, heval⟩ := VerifM.eval_bind_expectEq heval
    have heval_val : (compile env S val).eval st ρ _ := VerifM.eval_bind heval
    refine PrimitiveLaws.wp_bind_arraySet <| ?_
    have hstart := Scope.typed_dup W S st ρ γg γ R
    refine hstart.trans <| ihVal env W S γg γ (R := (S.typed W γg γ ∗ (R))) henv hS (VerifM.eval.decls_grow ρ heval_val) ?_
    intro v_val ρ_val st₁ sv hΨ_val hsv_wf heval_sv
    obtain ⟨hdecls_val, hagreeOn_val, hΨ_val⟩ := hΨ_val
    have heval_idx : (compile env S idx).eval st₁ ρ_val _ := VerifM.eval_bind hΨ_val
    have hS_val := Scope.wfIn_mono hS hdecls_val hagreeOn_val (VerifM.eval.wf hΨ_val).namesDisjoint
    have hstepB :=
      (Scope.typed_push W S st₁ ρ_val γg γ R v_val val.ty).trans
        (Scope.typed_dup W S st₁ ρ_val γg γ (TinyML.ValHasType W v_val val.ty ∗ R))
    refine hstepB.trans <| ihIdx env W S γg γ (R := (S.typed W γg γ ∗ ((TinyML.ValHasType W v_val val.ty ∗ R)))) henv hS_val (VerifM.eval.decls_grow ρ_val heval_idx) ?_
    intro v_idx ρ_idx st₂ si hΨ_idx hsi_wf heval_si
    obtain ⟨hdecls_idx, hagreeOn_idx, hΨ_idx⟩ := hΨ_idx
    have heval_arr : (compile env S arr).eval st₂ ρ_idx _ := VerifM.eval_bind hΨ_idx
    have hS_idx := Scope.wfIn_mono hS_val hdecls_idx hagreeOn_idx (VerifM.eval.wf hΨ_idx).namesDisjoint
    have hstepC := Scope.typed_push W S st₂ ρ_idx γg γ
      (TinyML.ValHasType W v_val val.ty ∗ R) v_idx idx.ty
    refine hstepC.trans <| ihArr env W S γg γ (R := (TinyML.ValHasType W v_idx idx.ty ∗ (TinyML.ValHasType W v_val val.ty ∗ R))) henv hS_idx (VerifM.eval.decls_grow ρ_idx heval_arr) ?_
    intro v_arr ρ_arr st₃ sa hΨ_arr hsa_wf heval_sa
    obtain ⟨hdecls_arr, hagreeOn_arr, hΨ_arr⟩ := hΨ_arr
    have hsi_wf₃ := Term.wfIn_mono si hsi_wf hdecls_arr (VerifM.eval.wf hΨ_arr).namesDisjoint
    have hsv_wf₃ : sv.wfIn st₃.decls :=
      Term.wfIn_mono sv hsv_wf (hdecls_idx.trans hdecls_arr) (VerifM.eval.wf hΨ_arr).namesDisjoint
    have hsv_wf₂ : sv.wfIn st₂.decls :=
      Term.wfIn_mono sv hsv_wf hdecls_idx (VerifM.eval.wf hΨ_idx).namesDisjoint
    have hsi_eval : si.eval ρ_arr = v_idx := by
      rw [Term.eval_agreeOn hsi_wf (Env.agreeOn_symm hagreeOn_arr)]; exact heval_si
    have hsv_eval : sv.eval ρ_arr = v_val := by
      rw [Term.eval_agreeOn hsv_wf₂ (Env.agreeOn_symm hagreeOn_arr)]
      rw [Term.eval_agreeOn hsv_wf (Env.agreeOn_symm hagreeOn_idx)]
      exact heval_sv
    obtain ⟨hi, hlt, hcont2⟩ := VerifM.eval_assertBounds (VerifM.eval_bind hΨ_arr) hsi_wf₃ hsa_wf
    have hfind := VerifM.eval_bind hcont2
    rw [hty, hidxty, ← helemTy]
    refine VerifM.eval_findMatchForce W
      (R := TinyML.ValHasType W v_arr (.ownedArray elemTy) ∗ TinyML.ValHasType W v_idx .int ∗
        TinyML.ValHasType W v_val elemTy ∗ R)
      (Φ := wp W.pctx (.arraySet (.val v_arr) (.val v_idx) (.val v_val)) Φ) hfind hsa_wf ?_

    intro contents st₄ hQ hdecls hcontents_wf
    let contents' : Term .value := .unop .ofVec
      (.terop .vecSet (.unop .toVec contents) (.unop .toInt si) sv)
    have hcontents'_wf : contents'.wfIn st₄.decls := by
      rw [hdecls]
      exact ⟨trivial, ⟨trivial, ⟨trivial, hcontents_wf⟩, ⟨trivial, hsi_wf₃⟩, hsv_wf₃⟩⟩
    have hatom_wf : (SpatialAtom.arrayPointsTo sa contents' elemTy).wfIn st₄.decls := by
      rw [hdecls]; exact ⟨hsa_wf, by simpa [hdecls] using hcontents'_wf⟩
    have hunit_wf : (Term.const .unit).wfIn st₄.decls := by simp [Term.wfIn, Const.wfIn]
    simpa [State.sl_eq] using
      (PrimitiveLaws.wp_arraySet_owned (W := W)
        (rest := st₄.owns) (arr := sa) (contents := contents) (contents' := contents')
        (idx := si) (val := sv) (elemTy := elemTy) (varr := v_arr) (vidx := v_idx)
        (vval := v_val) (Q := Φ) (R := R) heval_sa hsi_eval hsv_eval hi hlt rfl (by
          -- Acquire the updated atom, then conclude with the postcondition.
          have hstep := VerifM.eval_acquireSpatial W
            (R := TinyML.ValHasType W .unit .unit ∗ R)
            (Φ := Φ .unit) (VerifM.eval_bind hQ) hatom_wf
            (fun st₅ hq₅ hdecls₅ _howns₅ =>
              hpost .unit ρ_arr st₅ (.const .unit) (VerifM.eval_ret hq₅)
                (by rw [hdecls₅]; exact hunit_wf) (by simp [Term.eval]))
          simp only [SpatialContext.interp_insert]
          istart
          iintro ⟨⟨Hatom, Howns⟩, HunitTy, HR⟩
          iapply hstep
          isplitl [Hatom]
          · iexact Hatom
          · isplitl [Howns]
            · simp only [State.sl_eq]
              iexact Howns
            · iframe HunitTy HR))
  | prim _ | sum _ | arrow _ _ | ref _ | vec _ | owned _ | empty | value | tuple _ | tvar _
  | named _ _ =>
      intro env W S γg γ st ρ Ψ R Φ henv _hS heval _ _ _ _
      simp only [compile, hty] at heval
      exact (VerifM.eval_fatal (VerifM.eval_bind heval)).elim

theorem compileUnop_correct (op : TinyML.UnOp) (e : Expr) (uty : TinyML.Typ)
    (ih : correctExpr e) :
    correctExpr (.unop op e uty) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  have heval_e : (compile env S e).eval st ρ _ := VerifM.eval_bind heval
  refine PrimitiveLaws.wp_bind_unop <| ih env W S γg γ (R := R) henv hS (VerifM.eval.decls_grow ρ heval_e) ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se
  obtain ⟨_, _, hΨ_e⟩ := hΨ_e
  obtain ⟨ty, htypeOf, hΨ_e⟩ := VerifM.eval_bind_expectSome hΨ_e
  obtain ⟨hty_eq, hΨ_e⟩ := VerifM.eval_bind_expectEq hΨ_e
  obtain ⟨t, hcompUnop, hΨ_e⟩ := VerifM.eval_bind_expectSome hΨ_e
  obtain hΨ_e := VerifM.eval_ret hΨ_e
  have htyped :
      st₁.sl W ρ_e ∗ TinyML.ValHasType W v_e e.ty ∗ R ⊢
        st₁.sl W ρ_e ∗ iprop(∃ w, ⌜TinyML.evalUnOp op v_e = some w⌝ ∗ TinyML.ValHasType W w ty) ∗ R :=
    sep_mono_right (sep_mono_left (TinyML.evalUnOp_typed htypeOf))
  simp only [Expr.WithTypeVars.ty] at hpost
  refine htyped.trans ?_
  istart
  iintro ⟨Howns, Hex, HR⟩
  icases Hex with ⟨%w, %heval_op, Hwty⟩
  have ht_eval : t.eval ρ_e = w :=
    compileUnop_eval heval_se heval_op hcompUnop
  have hq : st₁.sl W ρ_e ∗ TinyML.ValHasType W w ty ∗ R ⊢ Φ w :=
    by simpa [hty_eq] using
      (hpost w ρ_e st₁ t hΨ_e (compileUnop_wfIn hse_wf hcompUnop) ht_eval)
  have hwp : st₁.sl W ρ_e ∗ TinyML.ValHasType W w ty ∗ R ⊢ wp W.pctx (.unop op (.val v_e)) Φ :=
    PrimitiveLaws.wp_unop
      (R := st₁.sl W ρ_e ∗ TinyML.ValHasType W w ty ∗ R)
      (Q := Φ) (op := op) (v := v_e) (res := w) hq heval_op
  iapply hwp
  iframe Howns Hwty HR

/-- The `wp` step shared by the integer binary operations the compiler guards
with an assertion. `folOp` is the operation the compiled term uses and `g` the
integer operation it must denote. -/
private theorem compileIntBinop_correct (W : TinyML.World) {R : iProp}
    {Φ : Runtime.Val → iProp} {Ψ : Term .value → State → Env → Prop}
    {st : State} {ρ : Env} {sl sr : Term .value} {vl vr : Runtime.Val}
    {op : TinyML.BinOp} (folOp : BinOp .int .int .int) (g : Int → Int → Int)
    (hpost : ∀ v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls → Term.eval ρ' se = v →
      st'.sl W ρ' ∗ TinyML.ValHasType W v .int ∗ R ⊢ Φ v)
    (hΨ : Ψ (.unop .ofInt (.binop folOp (.unop .toInt sl) (.unop .toInt sr))) st ρ)
    (hwft : (Term.unop .ofInt
      (.binop folOp (.unop .toInt sl) (.unop .toInt sr))).wfIn st.decls)
    (hop : ∀ a b : Int, vr = .int b → TinyML.evalBinOp op (.int a) (.int b) = some (.int (g a b)))
    (hterm : ∀ a b : Int, vl = .int a → vr = .int b →
      Term.eval ρ (.unop .ofInt (.binop folOp (.unop .toInt sl) (.unop .toInt sr)))
        = Runtime.Val.int (g a b)) :
    st.sl W ρ ∗ (TinyML.ValHasType W vl .int ∗ (TinyML.ValHasType W vr .int ∗ R)) ⊢
      wp W.pctx (.binop op (.val vl) (.val vr)) Φ := by
  istart
  iintro H
  icases H with ⟨Howns, Hvl, Hvr, HR⟩
  ihave Hvl_int := (TinyML.ValHasType.int W vl).1 $$ Hvl
  ihave Hvr_int := (TinyML.ValHasType.int W vr).1 $$ Hvr
  icases Hvl_int with ⟨%a, %hvl⟩
  icases Hvr_int with ⟨%b, %hvr⟩
  have hq : st.sl W ρ ∗ R ⊢ Φ (.int (g a b)) := by
    have hgoal :
        st.sl W ρ ∗ TinyML.ValHasType W (.int (g a b)) .int ∗ R ⊢ Φ (.int (g a b)) :=
      hpost (.int (g a b)) ρ st _ hΨ hwft (hterm a b hvl hvr)
    iintro ⟨Howns, HR⟩
    iapply hgoal
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · exact TinyML.ValHasType.int_intro W (g a b)
      · iexact HR
  have hopab := hop a b hvr
  subst hvl hvr
  iapply (PrimitiveLaws.wp_binop (vl := .int a) (vr := .int b) (res := .int (g a b)) hq)
  · exact hopab
  · iframe Howns HR

theorem compileBinop_correct (op : TinyML.BinOp) (l r : Expr) (bty : TinyML.Typ)
    (ihR : correctExpr r) (ihL : correctExpr l) :
    correctExpr (.binop op l r bty) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  have heval_r : (compile env S r).eval st ρ _ := VerifM.eval_bind heval
  have hstart := Scope.typed_dup W S st ρ γg γ R
  refine PrimitiveLaws.wp_bind_binop <| hstart.trans <|
    ihR env W S γg γ (R := (S.typed W γg γ ∗ R)) henv hS (VerifM.eval.decls_grow ρ heval_r) ?_
  intro vr ρ_r st₁ sr hΨ_r hsr_wf heval_sr
  obtain ⟨hdecls_r, hagreeOn_r, hΨ_r⟩ := hΨ_r
  have heval_l : (compile env S l).eval st₁ ρ_r _ := VerifM.eval_bind hΨ_r
  have hleftStart := Scope.typed_push W S st₁ ρ_r γg γ R vr r.ty
  have hS_r := Scope.wfIn_mono hS hdecls_r hagreeOn_r (VerifM.eval.wf hΨ_r).namesDisjoint
  refine hleftStart.trans <|
    ihL env W S γg γ (R := (TinyML.ValHasType W vr r.ty ∗ R)) henv hS_r (VerifM.eval.decls_grow ρ_r heval_l) ?_
  intro vl ρ_l st₂ sl hΨ_l hsl_wf heval_sl
  obtain ⟨hdecls_l, hagreeOn_l, hΨ_l⟩ := hΨ_l
  obtain ⟨ty, htypeOf, hΨ_l⟩ := VerifM.eval_bind_expectSome hΨ_l
  obtain ⟨hty_eq, hΨ_l'⟩ := VerifM.eval_bind_expectEq hΨ_l
  simp only [Expr.WithTypeVars.ty] at hpost
  have hsr_ρ_l : sr.eval ρ_l = vr := by
    rw [Term.eval_agreeOn hsr_wf (Env.agreeOn_symm hagreeOn_l)]
    exact heval_sr
  by_cases hdivmod : op = .div ∨ op = .mod
  · have hΨ_div :
          (do
            let i t := Term.unop UnOp.toInt t
            let fol_op := if op == TinyML.BinOp.div then BinOp.div else BinOp.mod
            VerifM.assert (.not (.eq .int (i sr) (.const (.i 0))))
            pure (Term.unop .ofInt (Term.binop fol_op (i sl) (i sr)))).eval st₂ ρ_l Ψ := by
      simpa [hdivmod] using hΨ_l'
    obtain ⟨hlty, hrty, hty_int⟩ :=
      TinyML.BinOp.typeOf_arith (by tauto) htypeOf
    have hassert_wf : (Formula.not (.eq .int (.unop .toInt sr) (.const (.i 0)))).wfIn st₂.decls := by
      simpa [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn] using
        (Term.wfIn_mono sr hsr_wf hdecls_l (VerifM.eval.wf hΨ_div).namesDisjoint)
    have ⟨hne_zero, hΨ_post⟩ := VerifM.eval_assert (VerifM.eval_bind hΨ_div) hassert_wf
    simp [Formula.eval, Term.eval, Const.eval] at hne_zero
    rw [hsr_ρ_l] at hne_zero
    obtain hΨ_post := VerifM.eval_ret hΨ_post
    have hbty : bty = .int := hty_eq.symm.trans hty_int
    have hwf_sr_l : sr.wfIn st₂.decls :=
      Term.wfIn_mono sr hsr_wf hdecls_l (VerifM.eval.wf hΨ_div).namesDisjoint
    subst hbty
    rcases hdivmod with rfl | rfl
    · simpa [hlty, hrty] using
        compileIntBinop_correct W BinOp.div (· / ·) hpost (by simpa using hΨ_post)
          (by simpa [Term.wfIn, BinOp.wfIn, UnOp.wfIn] using And.intro hsl_wf hwf_sr_l)
          (by intro a b hvr; subst hvr; simp [TinyML.evalBinOp, hne_zero])
          (by intro a b hvl hvr; subst hvl; subst hvr
              simp [Term.eval, UnOp.eval, BinOp.eval, heval_sl, hsr_ρ_l])
    · simpa [hlty, hrty] using
        compileIntBinop_correct W BinOp.mod (· % ·) hpost (by simpa using hΨ_post)
          (by simpa [Term.wfIn, BinOp.wfIn, UnOp.wfIn] using And.intro hsl_wf hwf_sr_l)
          (by intro a b hvr; subst hvr; simp [TinyML.evalBinOp, hne_zero])
          (by intro a b hvl hvr; subst hvl; subst hvr
              simp [Term.eval, UnOp.eval, BinOp.eval, heval_sl, hsr_ρ_l])
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
        st₂.sl W ρ_l ∗ (TinyML.ValHasType W vl l.ty ∗ (TinyML.ValHasType W vr r.ty ∗ R)) ⊢
          st₂.sl W ρ_l ∗ ((TinyML.ValHasType W vl l.ty ∗ TinyML.ValHasType W vr r.ty) ∗ R) := by
      iintro ⟨Howns, Hvl, Hvr, HR⟩
      isplitl [Howns]
      · iexact Howns
      · isplitl [Hvl Hvr]
        · iframe Hvl Hvr
        · iexact HR
    have htyped :
        st₂.sl W ρ_l ∗ (TinyML.ValHasType W vl l.ty ∗ (TinyML.ValHasType W vr r.ty ∗ R)) ⊢
          st₂.sl W ρ_l ∗ iprop(∃ w, ⌜TinyML.evalBinOp op vl vr = some w⌝ ∗ TinyML.ValHasType W w ty) ∗ R :=
      hprep.trans <|
        (sep_mono_right (sep_mono_left (TinyML.evalBinOp_typed
          (fun h => hndivmod (Or.inl h))
          (fun h => hndivmod (Or.inr h))
          htypeOf)) :
          st₂.sl W ρ_l ∗ ((TinyML.ValHasType W vl l.ty ∗ TinyML.ValHasType W vr r.ty) ∗ R) ⊢
            st₂.sl W ρ_l ∗ iprop(∃ w, ⌜TinyML.evalBinOp op vl vr = some w⌝ ∗ TinyML.ValHasType W w ty) ∗ R)
    have hwfst₂ : st₂.decls.wf := (VerifM.eval.wf hΨ_ndiv).namesDisjoint
    obtain hΨ_ndiv := VerifM.eval_ret hΨ_ndiv
    have hwf_sr_l : sr.wfIn st₂.decls :=
      Term.wfIn_mono sr hsr_wf hdecls_l hwfst₂
    refine htyped.trans ?_

    istart
    iintro ⟨Howns, Hex, HR⟩
    icases Hex with ⟨%w, %heval_op, Hwty⟩
    have ht_eval : t.eval ρ_l = w := compileOp_eval heval_sl hsr_ρ_l heval_op hcompOp
    have hq : st₂.sl W ρ_l ∗ TinyML.ValHasType W w ty ∗ R ⊢ Φ w := by
      simpa [hty_eq] using
        (hpost w ρ_l st₂ t hΨ_ndiv (compileOp_wfIn hsl_wf hwf_sr_l hcompOp) ht_eval)
    have hwp : st₂.sl W ρ_l ∗ TinyML.ValHasType W w ty ∗ R ⊢ wp W.pctx (.binop op (.val vl) (.val vr)) Φ :=
      PrimitiveLaws.wp_binop
        (R := st₂.sl W ρ_l ∗ TinyML.ValHasType W w ty ∗ R)
        (Q := Φ) (op := op) (vl := vl) (vr := vr) (res := w) hq heval_op
    iapply hwp
    iframe Howns Hwty HR

/-- A ghost binding is erased, so the run-time program is the body alone. The
    ghost expression's obligation is discharged in the scope it is written in
    and leaves an update, which the body's weakest precondition absorbs. -/
theorem compileLetInGhost_correct (b : Binder) (e body : Expr)
    (ihBody : correctExpr body) :
    correctExpr (.letIn .ghost b e body) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  simp only [compile] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  unfold Expr.WithTypeVars.runtime
  refine PrimitiveLaws.wp_bupd (BIBase.Entails.trans (Scope.typed_dup W S st ρ γg γ R)
    ((compileGhostExpr_correct e env W S γg γ (R := iprop(S.typed W γg γ ∗ R))
        (Φ := fun _ => wp W.pctx (body.runtime.subst γ) Φ) henv hS
        (VerifM.eval.decls_grow ρ (VerifM.eval_bind heval)) ?_).trans
      (bupd_mono (exists_elim fun _ => .rfl))))
  intro v st₁ ρ₁ t hΨ ht_wf ht_eval
  obtain ⟨hdecls, hagreeOn, hΨ⟩ := hΨ
  obtain ⟨_, hΨ⟩ := VerifM.eval_bind_expectEq hΨ
  have hS₁ := Scope.wfIn_mono hS hdecls hagreeOn (VerifM.eval.wf hΨ).namesDisjoint
  cases hname : b.name with
  | none =>
    simp [hname] at hΨ
    refine BIBase.Entails.trans ?_ (ihBody env W S γg γ henv hS₁ hΨ hpost)
    iintro ⟨Howns, _Hv, #HT, HR⟩
    iframe # ∗
  | some x =>
    simp [hname] at hΨ
    have hbody := VerifM.eval_define (VerifM.eval_bind hΨ) ht_wf
    rw [ht_eval] at hbody
    set x' := st₁.freshConst (some x) .value
    have hfresh : x'.name ∉ st₁.decls.allNames := st₁.freshConst_fresh (some x) .value
    have hagreeOn₂ : Env.agreeOn st₁.decls ρ₁ (ρ₁.updateConst .value x'.name v) :=
      Env.agreeOn_update_fresh_const hfresh
    have hS₂ := (Scope.wfIn_mono hS₁ (Signature.Subset.subset_addConst _ _) hagreeOn₂
      (VerifM.eval.wf hbody).namesDisjoint).bindGhost (x := x) (ty := e.ty) (v := v)
      (List.Mem.head _) rfl (by simp [x', Env.updateConst])
    refine BIBase.Entails.trans ?_ (ihBody env W (S.bindGhost x x' e.ty) (γg.update x v) γ
      henv hS₂ hbody hpost)
    iintro ⟨Howns, Hv, #HT, HR⟩
    isplitl [Howns]
    · simp only [State.sl_eq]
      iapply (SpatialContext.interp_agreeOn W (VerifM.eval.wf hΨ).ownsWf hagreeOn₂).1
      iexact Howns
    · isplitl [Hv]
      · iapply Scope.typed_bindGhost
        iframe # ∗
      · iexact HR

theorem compileLetIn_correct (b : Binder) (e body : Expr)
    (ihE : correctExpr e) (ihBody : correctExpr body) :
    correctExpr (.letIn .runtime b e body) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  simp only [compile] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.letIn_subst]
  refine PrimitiveLaws.wp_letIn ((Scope.typed_dup W S st ρ γg γ R).trans <|
    ihE env W S γg γ (R := S.typed W γg γ ∗ R) henv hS
      (VerifM.eval.decls_grow ρ (VerifM.eval_bind heval)) ?_)
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_e
  obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
  obtain ⟨_, hΨ_e⟩ := VerifM.eval_bind_expectEq hΨ_e
  have hS₁ := Scope.wfIn_mono hS hdecls_e hagreeOn_e (VerifM.eval.wf hΨ_e).namesDisjoint
  rw [Runtime.Expr.subst_remove'_updateBinder]
  cases hname : b.name with
  | none =>
    simp [hname] at hΨ_e
    rw [Binder.runtime_of_name_none hname]
    simp only [Runtime.Subst.updateBinder]
    refine BIBase.Entails.trans ?_ (ihBody env W S γg γ henv hS₁ hΨ_e hpost)
    iintro ⟨Howns, _Hv, #HT, HR⟩
    iframe # ∗
  | some x =>
    simp [hname] at hΨ_e
    have hbody := VerifM.eval_define (VerifM.eval_bind hΨ_e) hse_wf
    rw [heval_e] at hbody
    set x' := st₁.freshConst (some x) .value
    have hfresh : x'.name ∉ st₁.decls.allNames := st₁.freshConst_fresh (some x) .value
    have hagreeOn₂ : Env.agreeOn st₁.decls ρ_e (ρ_e.updateConst .value x'.name v_e) :=
      Env.agreeOn_update_fresh_const hfresh
    have hS₂ := (Scope.wfIn_mono hS₁ (Signature.Subset.subset_addConst _ _) hagreeOn₂
      (VerifM.eval.wf hbody).namesDisjoint).bindRuntime (x := x) (ty := e.ty) (v := v_e)
      (List.Mem.head _) rfl (by simp [x', Env.updateConst])
    rw [Binder.runtime_of_name_some hname]
    simp only [Runtime.Subst.updateBinder]
    refine BIBase.Entails.trans ?_ (ihBody env W (S.bindRuntime x x' e.ty) γg (γ.update x v_e)
      henv hS₂ hbody hpost)
    iintro ⟨Howns, Hv, #HT, HR⟩
    isplitl [Howns]
    · simp only [State.sl_eq]
      iapply (SpatialContext.interp_agreeOn W (VerifM.eval.wf hΨ_e).ownsWf hagreeOn₂).1
      iexact Howns
    · isplitl [Hv]
      · iapply Scope.typed_bindRuntime
        iframe # ∗
      · iexact HR

/-- The binders of a run-time `let` over a tuple, one run-time binder per named
component. -/
theorem compileProductBindersFrom_correct (env : Verifier.Env) (W : TinyML.World)
    (body : Expr) (ihBody : correctExpr body) :
    ∀ (names : List Binder) (tys : List TinyML.Typ) (se : Term .value) (i : Nat)
      (allVals vals : List Runtime.Val) (S : Scope) (γg γ : Runtime.Subst)
      (st : State) (ρ : Env)
      (Ψ : Term .value → State → Env → Prop) (R : iProp) (Φ : Runtime.Val → iProp),
      VerifM.eval (compileProductBindersFrom .runtime S names tys se i) st ρ
        (fun S' st' ρ' => (compile env S' body).eval st' ρ' Ψ) →
      env.wf W → S.wfIn W st.decls ρ γg γ →
      se.wfIn st.decls → se.eval ρ = .tuple allVals → allVals.drop i = vals →
      (∀ v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls → Term.eval ρ' se = v →
        st'.sl W ρ' ∗ TinyML.ValHasType W v body.ty ∗ R ⊢ Φ v) →
      st.sl W ρ ∗ (TinyML.ValsHaveTypes W vals tys ∗ (S.typed W γg γ ∗ R)) ⊢
        wp W.pctx
          (body.runtime.subst (γ.updateAllBinder (names.map Binder.WithTypeVars.runtime) vals)) Φ
  | [], [], se, i, allVals, vals, S, γg, γ, st, ρ, Ψ, R, Φ,
      heval, henv, hS, _hse_wf, _hse_eval, _hdrop, hpost => by
      simp only [compileProductBindersFrom] at heval
      cases vals with
      | nil =>
          simp only [List.map_nil, Runtime.Subst.updateAllBinder_nil_left]
          refine BIBase.Entails.trans ?_ (ihBody env W S γg γ henv hS (VerifM.eval_ret heval) hpost)
          iintro ⟨Hsl, Hvals, Hctx⟩
          ihave Hemp := (TinyML.ValsHaveTypes.nil W).1 $$ Hvals
          iframe
      | cons v vs =>
          iintro ⟨_Hsl, Hvals, _Hctx⟩
          ihave Hfalse := (TinyML.ValsHaveTypes.cons_nil W v vs).1 $$ Hvals
          iapply false_elim
          iexact Hfalse
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, heval, _, _, _, _, _, _ => by
      simp only [compileProductBindersFrom] at heval
      exact (VerifM.eval_fatal heval).elim
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, heval, _, _, _, _, _, _ => by
      simp only [compileProductBindersFrom] at heval
      exact (VerifM.eval_fatal heval).elim
  | b :: bs, ty :: tys, se, i, allVals, vals, S, γg, γ, st, ρ, Ψ, R, Φ,
      heval, henv, hS, hse_wf, hse_eval, hdrop, hpost => by
      cases vals with
      | nil =>
          iintro ⟨_Hsl, Hvals, _Hctx⟩
          ihave Hfalse := (TinyML.ValsHaveTypes.nil_cons W ty tys).1 $$ Hvals
          iapply false_elim
          iexact Hfalse
      | cons v vs =>
          simp only [compileProductBindersFrom] at heval
          obtain ⟨_, hcont⟩ := VerifM.eval_bind_expectEq heval
          have hhead_eval : (se.proj i).eval ρ = v :=
            Term.proj_eval hse_eval (by have := congrArg (·[0]?) hdrop; simpa using this)
          have htail_drop : allVals.drop (i + 1) = vs := by
            have := congrArg (List.drop 1) hdrop
            simpa [List.drop_drop, Nat.add_comm] using this
          simp only [List.map_cons, Runtime.Subst.updateAllBinder_cons]
          cases hname : b.name with
          | none =>
              simp [hname] at hcont
              rw [Binder.runtime_of_name_none hname]
              simp only [Runtime.Subst.updateBinder]
              refine BIBase.Entails.trans ?_ (compileProductBindersFrom_correct env W body
                ihBody bs tys se (i + 1) allVals vs S γg γ st ρ Ψ R Φ hcont henv hS hse_wf
                hse_eval htail_drop hpost)
              iintro ⟨Hsl, Hvals, Hctx⟩
              ihave Hpair := (TinyML.ValsHaveTypes.cons W v vs ty tys).1 $$ Hvals
              icases Hpair with ⟨_Hv, Hvs⟩
              iframe
          | some x =>
              simp [hname] at hcont
              have hrec := VerifM.eval_define (VerifM.eval_bind hcont) (Term.proj_wfIn hse_wf i)
              rw [hhead_eval] at hrec
              set x' := st.freshConst (some x) .value
              have hfresh : x'.name ∉ st.decls.allNames := st.freshConst_fresh (some x) .value
              have hagreeOn : Env.agreeOn st.decls ρ (ρ.updateConst .value x'.name v) :=
                Env.agreeOn_update_fresh_const hfresh
              have hwf₁ := (VerifM.eval.wf hrec).namesDisjoint
              have hS₁ := (Scope.wfIn_mono hS (Signature.Subset.subset_addConst _ _) hagreeOn
                hwf₁).bindRuntime (x := x) (ty := ty) (v := v) (List.Mem.head _) rfl
                (by simp [x', Env.updateConst])
              rw [Binder.runtime_of_name_some hname]
              simp only [Runtime.Subst.updateBinder]
              refine BIBase.Entails.trans ?_ (compileProductBindersFrom_correct env W body
                ihBody bs tys se (i + 1) allVals vs (S.bindRuntime x x' ty) γg (γ.update x v) _ _
                Ψ R Φ hrec henv hS₁
                (Term.wfIn_mono se hse_wf (Signature.Subset.subset_addConst _ _) hwf₁)
                (by rw [Term.eval_agreeOn hse_wf (Env.agreeOn_symm hagreeOn)]; exact hse_eval)
                htail_drop hpost)
              iintro ⟨Hsl, Hvals, #HT, HR⟩
              ihave Hpair := (TinyML.ValsHaveTypes.cons W v vs ty tys).1 $$ Hvals
              icases Hpair with ⟨Hv, Hvs⟩
              isplitl [Hsl]
              · simp only [State.sl_eq]
                iapply (SpatialContext.interp_agreeOn W (VerifM.eval.wf hcont).ownsWf hagreeOn).1
                iexact Hsl
              · isplitl [Hvs]
                · iexact Hvs
                · isplitl [Hv]
                  · iapply Scope.typed_bindRuntime
                    iframe # ∗
                  · iexact HR

theorem compileLetProd_correct (names : List Binder) (e body : Expr)
    (ihE : correctExpr e) (ihBody : correctExpr body) :
    correctExpr (.letProd names e body) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  simp only [compile] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.letProd_subst]
  have heval_e : (compile env S e).eval st ρ _ :=
    VerifM.eval_bind heval
  have hstart := Scope.typed_dup W S st ρ γg γ R
  refine PrimitiveLaws.wp_bind_letProd <| hstart.trans <|
    ihE env W S γg γ (R := (S.typed W γg γ ∗ R)) henv hS (VerifM.eval.decls_grow ρ heval_e) ?_
  intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se
  obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
  cases hty : e.ty with
  | tuple tys =>
      simp [hty] at hΨ_e
      have hprod_eval := VerifM.eval_bind (VerifM.eval_ret (VerifM.eval_bind hΨ_e))
      have hS_e := Scope.wfIn_mono hS hdecls_e hagreeOn_e (VerifM.eval.wf hΨ_e).namesDisjoint
      refine (show st₁.sl W ρ_e ∗
          (TinyML.ValHasType W v_e (.tuple tys) ∗
            (S.typed W γg γ ∗ R)) ⊢
            wp W.pctx
              (Runtime.Expr.letProd (names.map Binder.WithTypeVars.runtime) (.val v_e)
                (Runtime.Expr.subst (γ.removeAll' (names.map Binder.WithTypeVars.runtime)) body.runtime)) Φ from ?_)
      iintro ⟨Hsl, Hve, #HT, HR⟩
      ihave Htuple := (TinyML.ValHasType.tuple W v_e tys).1 $$ Hve
      icases Htuple with ⟨%vs, %hveq, Hvals⟩
      subst hveq
      ihave %hlen_vals := (TinyML.ValsHaveTypes.length_eq (W := W) (vs := vs) (ts := tys)) $$ Hvals
      have hnames_len : (names.map Binder.WithTypeVars.runtime).length = vs.length := by
        have hlen_compile := compileProductBindersFrom_length hse_wf hprod_eval
        simp [hlen_compile, hlen_vals]
      have hbody_subst := Runtime.Expr.subst_removeAll'_updateAllBinder body.runtime γ
        (names.map Binder.WithTypeVars.runtime) vs hnames_len
      iapply (PrimitiveLaws.wp_letProd_val (pctx := W.pctx)
        (names := names.map Binder.WithTypeVars.runtime) (vs := vs)
        (body := Runtime.Expr.subst (γ.removeAll' (names.map Binder.WithTypeVars.runtime)) body.runtime)
        hnames_len BIBase.Entails.rfl)
      rw [hbody_subst]
      iapply (compileProductBindersFrom_correct env W body ihBody names tys
        se 0 vs vs S γg γ st₁ ρ_e Ψ R Φ hprod_eval henv hS_e hse_wf heval_se rfl hpost)
      iframe # ∗
  | prim _ | sum _ | arrow _ _ | ref _ | array _ | ownedArray _ | vec _ | owned _ | empty | value | tvar _
  | named _ _ =>
      simp [hty] at hΨ_e
      exact (VerifM.eval_fatal (VerifM.eval_bind hΨ_e)).elim

theorem compileIfThenElse_correct (cond thn els : Expr) (ty : TinyML.Typ)
    (ihCond : correctExpr cond) (ihThn : correctExpr thn) (ihEls : correctExpr els) :
    correctExpr (.ifThenElse cond thn els ty) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  simp only [Expr.WithTypeVars.ty] at hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst]
  simp only [compile] at heval
  have heval_cond : (compile env S cond).eval st ρ _ := VerifM.eval_bind heval
  have hstart := Scope.typed_dup W S st ρ γg γ R
  refine PrimitiveLaws.wp_bind_if <| hstart.trans <|
    ihCond env W S γg γ (R := (S.typed W γg γ ∗ R)) henv hS (VerifM.eval.decls_grow ρ heval_cond) ?_
  intro v_c ρ_c st₁ sc hΨ_c hsc_wf heval_c
  obtain ⟨hdecls_c, hagreeOn_c, hΨ_c⟩ := hΨ_c
  have hS_c := Scope.wfIn_mono hS hdecls_c hagreeOn_c (VerifM.eval.wf hΨ_c).namesDisjoint
  obtain ⟨hcond_bool, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
  obtain ⟨hthn_ty, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
  obtain ⟨hels_ty, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
  have heval_branches : (VerifM.all [true, false]).eval st₁ ρ_c _ := VerifM.eval_bind hΨ_c
  have hall := VerifM.eval_all heval_branches
  have htrue := hall true (by simp)
  have hfalse := hall false (by simp)
  have hwf_ne : (Formula.not sc.isFalse).wfIn st₁.decls := by
    simp only [Term.isFalse, Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, _root_.and_true]
    exact hsc_wf
  have hwf_eq : sc.isFalse.wfIn st₁.decls := by
    simp only [Term.isFalse, Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, _root_.and_true]
    exact hsc_wf
  have htrue_cont := VerifM.eval_assumePure (VerifM.eval_bind htrue)
  have hfalse_cont := VerifM.eval_assumePure (VerifM.eval_bind hfalse)
  let φ_eq : Formula := sc.isFalse
  let st_thn : State := { st₁ with asserts := φ_eq.not :: st₁.asserts }
  let st_els : State := { st₁ with asserts := φ_eq :: st₁.asserts }
  have hbool_cases_bool :
      st₁.sl W ρ_c ∗
          (TinyML.ValHasType W v_c .bool ∗
            (S.typed W γg γ ∗ R)) ⊢
        st₁.sl W ρ_c ∗ iprop(⌜v_c = .bool false ∨ v_c = .bool true⌝) ∗
          (S.typed W γg γ ∗ R) := by
    iintro ⟨Howns, Hv, #HT, HR⟩
    ihave Hv_bool := (TinyML.ValHasType.bool W v_c).1 $$ Hv
    icases Hv_bool with ⟨%b, %hv⟩
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · exact pure_intro (by subst hv; cases b <;> simp)
      · iframe HT HR
  have hbool_cases :
      st₁.sl W ρ_c ∗ (TinyML.ValHasType W v_c cond.ty ∗ (S.typed W γg γ ∗ R)) ⊢
        st₁.sl W ρ_c ∗ iprop(⌜v_c = .bool false ∨ v_c = .bool true⌝) ∗
          (S.typed W γg γ ∗ R) := by
    simpa [hcond_bool] using hbool_cases_bool
  refine hbool_cases.trans ?_
  istart
  iintro ⟨Howns, Hbool, #HT, HR⟩
  icases Hbool with %hbool
  rcases hbool with hfalse_val | htrue_val
  · subst hfalse_val
    have heval_els : (compile env S els).eval st_els ρ_c Ψ :=
      hfalse_cont hwf_eq (by
        simp only [Term.isFalse, Formula.eval, Term.eval, UnOp.eval, Const.eval]
        exact heval_c)
    have hwp :
        st_els.sl W ρ_c ∗ (S.typed W γg γ ∗ R) ⊢
          wp W.pctx (.ifThenElse (.val (.bool false)) (thn.runtime.subst γ) (els.runtime.subst γ)) Φ :=
      PrimitiveLaws.wp_if_false
        (thn := thn.runtime.subst γ) (els := els.runtime.subst γ) <|
        ihEls env W S γg γ (Ψ := Ψ) (R := R) (Φ := Φ) henv hS_c heval_els
          (fun v ρ' st' se hΨ hs hw =>
            by simpa [hels_ty] using hpost v ρ' st' se hΨ hs hw)
    have hctx :
        st₁.sl W ρ_c ∗ (S.typed W γg γ ∗ R) ⊢
          st_els.sl W ρ_c ∗ (S.typed W γg γ ∗ R) := by
      simp [st_els, State.sl]
    iapply (hctx.trans hwp)
    iframe Howns HT HR
  · subst htrue_val
    have heval_ne : sc.eval ρ_c ≠ Runtime.Val.bool false := by
      rw [heval_c]
      simp
    have heval_thn : (compile env S thn).eval st_thn ρ_c Ψ :=
      htrue_cont hwf_ne (by
        simp only [Term.isFalse, Formula.eval, Term.eval, UnOp.eval, Const.eval]
        exact heval_ne)
    have hwp :
        st_thn.sl W ρ_c ∗ (S.typed W γg γ ∗ R) ⊢
          wp W.pctx (.ifThenElse (.val (.bool true)) (thn.runtime.subst γ) (els.runtime.subst γ)) Φ :=
      PrimitiveLaws.wp_if_true
        (thn := thn.runtime.subst γ) (els := els.runtime.subst γ) <|
        ihThn env W S γg γ (Ψ := Ψ) (R := R) (Φ := Φ) henv hS_c heval_thn
          (fun v ρ' st' se hΨ hs hw =>
            by simpa [hthn_ty] using hpost v ρ' st' se hΨ hs hw)
    have hctx :
        st₁.sl W ρ_c ∗ (S.typed W γg γ ∗ R) ⊢
          st_thn.sl W ρ_c ∗ (S.typed W γg γ ∗ R) := by
      simp [st_thn, State.sl]
    iapply (hctx.trans hwp)
    iframe Howns HT HR

theorem compileTuple_correct (es : List Expr)
    (ihEs : correctExprs es) :
    correctExpr (.tuple es) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  simp only [Expr.WithTypeVars.ty] at hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst, List.map_map]
  simp only [compile] at heval
  have heval_es : (compileExprs env S es).eval st ρ _ := VerifM.eval_bind heval
  refine PrimitiveLaws.wp_bind_tuple <| ihEs env W S γg γ (R := R) henv hS (VerifM.eval.decls_grow ρ heval_es) ?_
  intro vs ρ' st' terms hΨ hwf_terms heval_terms
  obtain ⟨_, _, hΨ⟩ := hΨ
  obtain hΨ := VerifM.eval_ret hΨ
  have heval_tuple : (Term.tuple terms).eval ρ' = Runtime.Val.tuple vs :=
    Term.tuple_eval heval_terms
  have hwf_tuple : (Term.tuple terms).wfIn st'.decls := Term.tuple_wfIn hwf_terms
  refine PrimitiveLaws.wp_tuple ?_
  have hstep :
      st'.sl W ρ' ∗ TinyML.ValsHaveTypes W vs (es.map Expr.WithTypeVars.ty) ∗ (R) ⊢
        st'.sl W ρ' ∗ TinyML.ValHasType W (.tuple vs) (.tuple (es.map Expr.WithTypeVars.ty)) ∗ R := by
    iintro ⟨Howns, Hvals, HR⟩
    isplitl [Howns]
    · iexact Howns
    · isplitl [Hvals]
      · iapply (TinyML.ValHasType.tuple W (.tuple vs) (es.map Expr.WithTypeVars.ty)).2
        iexists vs
        isplitr
        · ipureintro; rfl
        · iexact Hvals
      · iexact HR
  exact hstep.trans <|
    hpost (Runtime.Val.tuple vs) ρ' st' (Term.tuple terms)
      hΨ hwf_tuple heval_tuple


/-- Application of a function expression whose type carries a specification: the
    arguments and then the function are evaluated, and the function value's own
    interpretation — which is exactly its specification — supplies the call. -/
theorem compileAppSpec_correct
    (fn : Expr) (args gargs : List Expr) (aty : TinyML.Typ)
    (argTys : List TinyML.Typ) (retTy : TinyML.Typ) (s : Spec TinyML.Typ)
    (hfnty : fn.ty = .arrow argTys retTy (some s))
    (ihFn : correctExpr fn) (ihArgs : correctExprs args)
    (env : Verifier.Env) (W : TinyML.World) (S : Scope) (γg γ : Runtime.Subst)
    {st : State} {ρ : Env} {Ψ : Term .value → State → Env → Prop} {R : iProp}
    {Φ : Runtime.Val → iProp} (henv : env.wf W) (hS : S.wfIn W st.decls ρ γg γ)
    (heval : VerifM.eval
      (do
        VerifM.expectEq "app type annotation mismatch" retTy aty
        VerifM.expectEq "specification arity mismatch" s.args.length argTys.length
        let sterms ← compileExprs env S args
        let _ ← compile env S fn
        let gterms ← compileGhostExprs env S gargs
        let r ← Spec.call (FiniteSubst.base env.signature) argTys retTy s
          ((args.map Expr.WithTypeVars.ty).zip sterms)
          ((gargs.map Expr.WithTypeVars.ty).zip gterms)
        pure r.2) st ρ Ψ)
    (hswf : s.wfIn env.signature)
    (hpost : ∀ v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls → Term.eval ρ' se = v →
      st'.sl W ρ' ∗ TinyML.ValHasType W v aty ∗ R ⊢ Φ v) :
    st.sl W ρ ∗ (S.typed W γg γ ∗ R) ⊢
      wp W.pctx (.app (fn.runtime.subst γ) (args.map (fun e => e.runtime.subst γ))) Φ := by
  obtain ⟨reg, Θ, Δ, ls, fns, lfs, gls⟩ := env
  obtain ⟨-, -, -, rfl, rfl, -, -, -⟩ := id henv
  obtain ⟨hret_eq, heval⟩ := VerifM.eval_bind_expectEq heval
  obtain ⟨hlen_e, heval⟩ := VerifM.eval_bind_expectEq heval
  have heval_args : (compileExprs _ S args).eval st ρ _ :=
    VerifM.eval_bind heval
  refine PrimitiveLaws.wp_bind_app ?_
  -- The typing context is persistent, so it can also travel in the frame.
  have hctx : st.sl W ρ ∗ (S.typed W γg γ ∗ R) ⊢
      st.sl W ρ ∗ (S.typed W γg γ ∗
        (S.typed W γg γ ∗ R)) := by
    istart
    iintro ⟨Howns, #HT, HR⟩
    iframe Howns HT HR
  refine hctx.trans <|
    ihArgs _ W S γg γ (R := (S.typed W γg γ ∗ R)) henv hS (VerifM.eval.decls_grow ρ heval_args) ?_
  intro vs ρ_args st_args sargs hΨ_args hsargs_wf heval_sargs
  obtain ⟨hdecls_args, hagreeOn_args, hΨ_args⟩ := hΨ_args
  have hag_args : W.agrees st_args.decls ρ_args := hS.agrees.step hdecls_args hagreeOn_args
  have hS_args := Scope.wfIn_mono hS hdecls_args hagreeOn_args (VerifM.eval.wf hΨ_args).namesDisjoint
  have heval_fn : (compile _ S fn).eval st_args ρ_args _ :=
    VerifM.eval_bind hΨ_args
  have hlen_sargs : sargs.length = vs.length := by
    simpa [Term.evalList] using List.Forall₂.length_eq heval_sargs
  -- The ghost arguments are compiled after the function, so the scope's typing
  -- has to survive the function's own compilation: it travels in the frame.
  have hctx' : st_args.sl W ρ_args ∗ TinyML.ValsHaveTypes W vs (args.map Expr.WithTypeVars.ty) ∗
      ((S.typed W γg γ ∗ R)) ⊢
      st_args.sl W ρ_args ∗ (S.typed W γg γ ∗
        (S.typed W γg γ ∗
          (TinyML.ValsHaveTypes W vs (args.map Expr.WithTypeVars.ty) ∗ R))) := by
    istart
    iintro ⟨Howns, #Hvals, #HT, HR⟩
    iframe Howns HT Hvals HR
  refine hctx'.trans <|
    ihFn _ W S γg γ (R := (S.typed W γg γ ∗
        (TinyML.ValsHaveTypes W vs (args.map Expr.WithTypeVars.ty) ∗ R))) henv hS_args (VerifM.eval.decls_grow ρ_args heval_fn) ?_
  intro fval ρ_fn st_fn sfn hΨ_fn _hsfn_wf _heval_sfn
  obtain ⟨hdecls_fn, hagreeOn_fn, hΨ_fn⟩ := hΨ_fn
  have hag_fn : W.agrees st_fn.decls ρ_fn := hag_args.step hdecls_fn hagreeOn_fn
  have hst_fn_wf : st_fn.decls.wf := (VerifM.eval.wf hΨ_fn).namesDisjoint
  have hS_fn := Scope.wfIn_mono hS_args hdecls_fn hagreeOn_fn hst_fn_wf
  have heval_gargs := VerifM.eval_bind hΨ_fn
  -- The ghost arguments are ghost code: they take no step, and the update their
  -- obligation leaves is absorbed by the call's weakest precondition.
  refine PrimitiveLaws.wp_bupd (BIBase.Entails.trans ?_
    ((compileGhostExprs_correct gargs _ W S γg γ
        (R := iprop(TinyML.ValHasType W fval fn.ty ∗
          (TinyML.ValsHaveTypes W vs (args.map Expr.WithTypeVars.ty) ∗ R)))
        (Φ := fun _ => wp W.pctx ((Runtime.Expr.val fval).app (vs.map Runtime.Expr.val)) Φ)
        henv hS_fn (VerifM.eval.decls_grow ρ_fn heval_gargs) ?_).trans
      (bupd_mono (exists_elim fun _ => .rfl))))
  · iintro ⟨Howns, #Hfval, #HT, #Hvals, HR⟩
    iframe Howns HT Hfval Hvals HR
  intro gs st_g ρ_g gterms hΨ_g hgterms_wf heval_gterms
  obtain ⟨hdecls_g, hagreeOn_g, hΨ_g⟩ := hΨ_g
  set typedArgs := (args.map Expr.WithTypeVars.ty).zip sargs with htypedArgs_def
  set typedGArgs := (gargs.map Expr.WithTypeVars.ty).zip gterms with htypedGArgs_def
  have hag_g : W.agrees st_g.decls ρ_g := hag_fn.step hdecls_g hagreeOn_g
  have hst_g_wf : st_g.decls.wf := (VerifM.eval.wf hΨ_g).namesDisjoint
  have hsargs_wf_g : ∀ t ∈ sargs, t.wfIn st_g.decls := fun t ht =>
    Term.wfIn_mono t (hsargs_wf t ht) (hdecls_fn.trans hdecls_g) hst_g_wf
  have htypedArgs_wf : ∀ p ∈ typedArgs, p.2.wfIn st_g.decls := by
    intro p hp
    exact hsargs_wf_g _ (List.of_mem_zip hp).2
  have htypedGArgs_wf : ∀ p ∈ typedGArgs, p.2.wfIn st_g.decls := by
    intro p hp
    exact hgterms_wf _ (List.of_mem_zip hp).2
  have hwf_pred : PredTrans.wfIn
      ((W.Δ_spec.declVars (FiniteSubst.base W.Δ_spec).dom).declVars
        (Spec.argVars s.allArgs)) s.pred := by
    simpa [FiniteSubst.base, Signature.declVars] using hswf
  have hbase_wf : (FiniteSubst.base W.Δ_spec).wfIn W.Δ_spec st_g.decls :=
    FiniteSubst.base_wfIn (hag_g.subset) henv.world.wf hst_g_wf henv.world.vars
  have hcall_eval : VerifM.eval
      (Spec.call (FiniteSubst.base W.Δ_spec) argTys retTy s typedArgs typedGArgs) st_g ρ_g
      (fun p st' ρ' => VerifM.eval (pure p.2) st' ρ' Ψ) := VerifM.eval_bind hΨ_g
  have hcall := Spec.call_correct W argTys retTy s W.Δ_spec (FiniteSubst.base W.Δ_spec)
    typedArgs typedGArgs st_g ρ_g (fun p st' ρ' => VerifM.eval (pure p.2) st' ρ' Ψ) Φ R
    hlen_e hwf_pred hbase_wf htypedArgs_wf htypedGArgs_wf hcall_eval
    (fun v st' ρ' t hΨ hwft heval => by
      have h := hpost v ρ' st' t (VerifM.eval_ret hΨ) hwft heval
      rw [← hret_eq] at h
      iintro H
      icases H with ⟨Howns', Hrest⟩
      icases Hrest with ⟨HR', Hty⟩
      iapply h
      iframe Howns' Hty HR')
  obtain ⟨hsub_ty, hsub_gty, happly⟩ := hcall
  have hreorder : st_g.sl W ρ_g ∗ (TinyML.ValsHaveTypes W gs (gargs.map Expr.WithTypeVars.ty) ∗
      (TinyML.ValHasType W fval fn.ty ∗
        (TinyML.ValsHaveTypes W vs (args.map Expr.WithTypeVars.ty) ∗ R))) ⊢
      st_g.sl W ρ_g ∗ (TinyML.ValHasType W fval fn.ty ∗
        (TinyML.ValsHaveTypes W gs (gargs.map Expr.WithTypeVars.ty) ∗
          (TinyML.ValsHaveTypes W vs (args.map Expr.WithTypeVars.ty) ∗ R))) := by
    istart
    iintro ⟨Howns, #Hgvals, #Hfval, #Hvals, HR⟩
    iframe Howns Hfval Hgvals Hvals HR
  refine hreorder.trans ?_
  rw [hfnty]
  refine (sep_mono_right (sep_mono_left
    (TinyML.ValHasType.arrow_some W fval argTys retTy s).1)).trans ?_
  unfold Spec.isPrecondFor
  istart
  iintro ⟨Howns, #Hspec, #Hgvals, #Hvals, HR⟩
  ihave Hlen := TinyML.ValsHaveTypes.length_eq $$ Hvals
  ipure Hlen
  ihave Hglen := TinyML.ValsHaveTypes.length_eq $$ Hgvals
  ipure Hglen
  have hlen_typed : (args.map Expr.WithTypeVars.ty).length = sargs.length := by
    rw [← Hlen]; exact hlen_sargs.symm
  have hlen_gtyped : (gargs.map Expr.WithTypeVars.ty).length = gterms.length := by
    rw [← Hglen]
    simpa [Term.evalList] using (List.Forall₂.length_eq heval_gterms).symm
  obtain ⟨hfst, heval_args_map⟩ := typedArgs_split hlen_typed heval_sargs
  obtain ⟨hgfst, heval_gargs_map⟩ := typedArgs_split hlen_gtyped heval_gterms
  have hsub_ty' : args.map Expr.WithTypeVars.ty = argTys := by
    simpa [htypedArgs_def, hfst] using hsub_ty
  have hsub_gty' : gargs.map Expr.WithTypeVars.ty = s.ghost.map Prod.snd := by
    simpa [htypedGArgs_def, hgfst] using hsub_gty
  -- The argument terms still denote the same values in the state the call is
  -- made in; the ghost arguments were compiled there, so they need no transport.
  have heval_sargs_map : typedArgs.map (fun p => p.2.eval ρ_g) = vs := by
    refine Eq.trans (List.map_congr_left fun p hp => ?_) heval_args_map
    exact Term.eval_agreeOn (hsargs_wf _ (List.of_mem_zip hp).2)
      (Env.agreeOn_symm (Env.agreeOn_trans hagreeOn_fn (Env.agreeOn_mono hdecls_fn hagreeOn_g)))
  have happly' :
      st_g.sl W ρ_g ∗ R ⊢
        PredTrans.apply (TinyML.ValHasType W) (fun r => TinyML.ValHasType W r retTy -∗ Φ r)
          s.pred (Spec.argsEnv ρ_g s.allArgs (vs ++ gs)) := by
    rw [heval_sargs_map, heval_gargs_map] at happly
    exact happly
  have hagree_ρ_g : Env.agreeOn W.Δ_spec W.ρ_spec ρ_g := hag_g.agree
  ispecialize Hspec $$ %ρ_g
  ispecialize Hspec $$ %Φ
  ispecialize Hspec $$ %vs
  ispecialize Hspec $$ %gs
  iapply Hspec
  · ipureintro
    exact hagree_ρ_g
  · ipureintro
    have := congrArg List.length hsub_ty'
    omega
  · ipureintro
    have := congrArg List.length hsub_gty'
    simp only [List.length_map] at this Hglen
    omega
  · iapply later_intro
    rw [← hsub_ty']
    iexact Hvals
  · iapply later_intro
    rw [← hsub_gty']
    iexact Hgvals
  · iapply later_intro
    iapply happly'
    iframe Howns HR

theorem compileApp_correct
    (fn : Expr) (args gargs : List Expr) (aty : TinyML.Typ)
    (ihFn : correctExpr fn)
    (ihArgs : correctExprs args) :
    correctExpr (.app fn args gargs aty) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  simp only [Expr.WithTypeVars.ty] at hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Runtime.Expr.subst, List.map_map]
  simp only [compile] at heval
  split at heval
  case _ argTys retTy s hfnty =>
    cases hcheck : Spec.checkWf s env.signature with
    | error msg => rw [hcheck] at heval; exact (VerifM.eval_fatal heval).elim
    | ok u =>
      cases u
      rw [hcheck] at heval
      exact compileAppSpec_correct fn args gargs aty argTys retTy s hfnty ihFn ihArgs
        env W S γg γ henv hS heval (Spec.checkWf_ok hcheck) hpost
  case _ =>
  cases fn with
  | prim n inst fty =>
    obtain ⟨reg, Θ, Δ, ls, fns, lfs, gls⟩ := env
    obtain ⟨-, -, -, rfl, rfl, -, -, -⟩ := id henv
    obtain ⟨i, hilookup, heval⟩ := VerifM.eval_bind_expectSome heval
    obtain ⟨u, hmode, heval⟩ := VerifM.eval_bind_expectSome heval
    cases u
    obtain ⟨hret_eq, heval⟩ := VerifM.eval_bind_expectEq heval
    obtain ⟨_hgargs_nil, heval⟩ := VerifM.eval_bind_expectEq heval
    have heval_args : (compileExprs _ S args).eval st ρ _ :=
      VerifM.eval_bind heval
    have hi_mem : i ∈ reg := Verifier.Registry.mem_of_lookup? hilookup
    have hisound := Verifier.Registry.Sound.get henv.sound hi_mem
    simp only [Expr.WithTypeVars.runtime, Runtime.Expr.subst_val]
    refine PrimitiveLaws.wp_bind_app ?_
    refine ihArgs _ W S γg γ (R := R) henv hS (VerifM.eval.decls_grow ρ heval_args) ?_
    intro vs ρ_args st_args sargs hΨ_args hsargs_wf heval_sargs
    obtain ⟨hdecls_args, hagreeOn_args, hΨ_args⟩ := hΨ_args
    let σi : TinyML.TyVar → TinyML.Typ := fun v => (inst.lookup v).getD .empty
    let argTys := i.argTys.map (TinyML.Typ.subst σi)
    let retTy := TinyML.Typ.subst σi i.retTy
    let typedArgs := (args.map Expr.WithTypeVars.ty).zip sargs
    have hlen_sargs : sargs.length = vs.length := by
      simpa [Term.evalList] using List.Forall₂.length_eq heval_sargs
    have hΔspec_args : W.Δ_spec.Subset st_args.decls := hS.agrees.subset.trans hdecls_args
    have hst_args_wf : st_args.decls.wf := (VerifM.eval.wf hΨ_args).namesDisjoint
    have hlen_i : i.spec.args.length = argTys.length := by
      simp only [argTys, List.length_map]; exact hisound.arg_len
    have hwf_pred :
        PredTrans.wfIn ((W.Δ_spec.declVars (FiniteSubst.base W.Δ_spec).dom).declVars
          (Spec.argVars i.spec.allArgs)) i.spec.pred := by
      simpa [FiniteSubst.base, Signature.declVars, Verifier.Intrinsic.specArgs] using
        hisound.spec_wf W.Δ_spec
          (Verifier.Registry.sigOf_subset_of_symSubset henv.symbols) henv.world.wf
    have hbase_wf : (FiniteSubst.base W.Δ_spec).wfIn W.Δ_spec st_args.decls :=
      FiniteSubst.base_wfIn hΔspec_args henv.world.wf hst_args_wf henv.world.vars
    have htypedArgs_wf : ∀ p ∈ typedArgs, p.2.wfIn st_args.decls := by
      intro p hp
      have hp'' : p.2 ∈ sargs := (List.of_mem_zip hp).2
      exact hsargs_wf _ hp''
    have hcall_eval : VerifM.eval
        (Spec.call (FiniteSubst.base W.Δ_spec) argTys retTy i.spec typedArgs []) st_args ρ_args
        (fun p st' ρ' => VerifM.eval (pure p.2) st' ρ' Ψ) := VerifM.eval_bind hΨ_args
    have hcall := Spec.call_correct W argTys retTy i.spec W.Δ_spec (FiniteSubst.base W.Δ_spec)
      typedArgs [] st_args ρ_args
      (fun p st' ρ' => VerifM.eval (pure p.2) st' ρ' Ψ) Φ R
      hlen_i hwf_pred hbase_wf htypedArgs_wf nofun hcall_eval
      (fun v st' ρ' t hΨ hwft heval => by
        have hret_eq' : retTy = aty := hret_eq
        have h := hpost v ρ' st' t (VerifM.eval_ret hΨ) hwft heval
        rw [← hret_eq'] at h
        iintro H
        icases H with ⟨Howns', Hrest⟩
        icases Hrest with ⟨HR', Hty⟩
        iapply h
        iframe Howns' Hty HR')
    obtain ⟨hsub_ty, hsub_gty, happly⟩ := hcall
    -- The call passes no ghost argument, so the intrinsic declares none.
    have hghost_nil : i.spec.ghost = [] := by simpa using hsub_gty.symm
    simp only [Spec.allArgs, hghost_nil, List.map_nil, List.append_nil] at happly
    refine PrimitiveLaws.wp_val ?_
    rw [henv.primitives]
    refine BIBase.Entails.trans ?_ (Verifier.Registry.wp_prim reg henv.sound
      (fun i' hi' => by
        rw [hilookup] at hi'
        cases hi'
        exact Verifier.Intrinsic.Mode.ne_ghost_of_runtime? hmode))
    show _ ⊢ reg.wpCtx n vs Φ
    have hctx_eq : reg.wpCtx n vs Φ = i.toPre vs Φ := by
      simp only [Verifier.Registry.wpCtx, hilookup]
    rw [hctx_eq]
    istart
    iintro ⟨Howns, Hvals, HR⟩
    iintuitionistic Hvals
    ihave Hlen := TinyML.ValsHaveTypes.length_eq $$ Hvals
    ipure Hlen
    have hlen_typed : (args.map Expr.WithTypeVars.ty).length = sargs.length := by
      rw [← Hlen]; exact hlen_sargs.symm
    obtain ⟨hfst, heval_sargs_map⟩ := typedArgs_split hlen_typed heval_sargs
    have hsub_ty' : args.map Expr.WithTypeVars.ty = argTys := by
      simpa [typedArgs, hfst] using hsub_ty
    have happly' :
        st_args.sl W ρ_args ∗ R ⊢
          PredTrans.apply (TinyML.ValHasType W) (fun r => TinyML.ValHasType W r retTy -∗ Φ r) i.spec.pred
            (Spec.argsEnv ρ_args i.spec.args vs) := by
      rw [heval_sargs_map] at happly
      exact happly
    have hagree_ρ_args : Env.agreeOn W.Δ_spec W.ρ_spec ρ_args :=
      (hS.agrees.step hdecls_args hagreeOn_args).agree
    have hρ_args_reg : ∀ d ∈ reg, ρ_args.respects d.symbol := by
      intro d hd
      exact Env.respects_of_agreeOn_extendWithSym
        (henv.interpretations d hd) (henv.symbols d hd) hagree_ρ_args
    iapply (show
        TinyML.ValsHaveTypes W vs argTys ∗
          PredTrans.apply (TinyML.ValHasType W) (fun r => TinyML.ValHasType W r retTy -∗ Φ r) i.spec.pred
            (Spec.argsEnv ρ_args i.spec.args vs) ⊢ i.toPre vs Φ from
        hisound.spec_sound σi W vs ρ_args Φ hρ_args_reg)
    isplitl [Hvals]
    · rw [← hsub_ty']
      iexact Hvals
    · iapply happly'
      iframe Howns HR
  | _ =>
    exact (VerifM.eval_fatal heval).elim

theorem compileMatch_correct (scrut : Expr) (branches : List (Binder × Expr)) (ty : TinyML.Typ)
    (ihScrut : correctExpr scrut) (ihBranches : correctBranches branches) :
    correctExpr (.match_ scrut branches ty) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  simp only [Expr.WithTypeVars.ty] at hpost
  unfold Expr.WithTypeVars.runtime
  simp only [Expr.branchListRuntime_eq_map, Runtime.Expr.subst, List.map_map]
  simp only [compile] at heval
  have heval_scrut : (compile env S scrut).eval st ρ _ := VerifM.eval_bind heval
  refine PrimitiveLaws.wp_bind_match <| BIBase.Entails.trans ?_ <|
    ihScrut env W S γg γ (R := (S.typed W γg γ ∗ R)) henv hS (VerifM.eval.decls_grow ρ heval_scrut) ?_
  · exact Scope.typed_dup W S st ρ γg γ R
  intro v_scrut ρ_scrut st_scrut se_scrut hΨ_scrut hse_wf heval_se
  obtain ⟨hdecls_scrut, hagreeOn_scrut, hΨ_scrut⟩ := hΨ_scrut
  cases hscrut_ty : sumComponents? env.typeDeclarations scrut.ty with
  | none =>
    simp only [hscrut_ty] at hΨ_scrut
    exact (VerifM.eval_fatal hΨ_scrut).elim
  | some ts =>
    simp [hscrut_ty] at hΨ_scrut
    by_cases hlen : ts.length ≠ branches.length
    · simp [hlen] at hΨ_scrut
      exact (VerifM.eval_fatal hΨ_scrut).elim
    · push Not at hlen
      by_cases htys : ∀ br ∈ branches, br.2.ty = ty
      · have hΨ_scrut' :
            (do
              let i ← VerifM.all (List.range (compileBranches env S se_scrut ts branches 0).length)
              match (compileBranches env S se_scrut ts branches 0)[i]? with
              | some m => m
              | none => VerifM.fatal "match branch index out of range").eval st_scrut ρ_scrut Ψ := by
          simpa [if_pos hlen, if_pos htys] using hΨ_scrut
        have hcb := compileBranches_length_get env S se_scrut ts branches 0
        have hactions_len := hcb.1
        have heval_all := VerifM.eval_bind hΨ_scrut'
        have hall := VerifM.eval_all heval_all
        exact (by
          iintro ⟨Hsl, Hscrut, #HT, HR⟩
          ihave Hscrut_sum :=
            ((valHasType_sumComponents (henv.typeDeclarations ▸ hscrut_ty)).1.trans
              (TinyML.ValHasType.sum W v_scrut ts).1) $$ Hscrut
          icases Hscrut_sum with ⟨%tag, %v_payload, %hval_eq, Hsum⟩
          ihave %htag_bound := TinyML.ValSumRel.bound $$ Hsum
          have htag_branches : tag < branches.length := hlen ▸ htag_bound
          have htag_range : tag ∈ List.range (compileBranches env S se_scrut ts branches 0).length := by
            rw [hactions_len]
            exact List.mem_range.mpr htag_branches
          have heval_tag := hall tag htag_range
          have hcb_get := hcb.2 tag htag_branches
          simp [hcb_get, show branches[tag]? = some branches[tag] from
            List.getElem?_eq_some_iff.mpr ⟨htag_branches, rfl⟩] at heval_tag
          have hget : ts[tag]? = some (ts[tag]?.getD .value) := by
            rw [List.getElem?_eq_getElem htag_bound]
            simp
          have hS_scrut := Scope.wfIn_mono hS hdecls_scrut hagreeOn_scrut
            (VerifM.eval.wf hΨ_scrut).namesDisjoint
          have hbranch_wp := ihBranches env W S γg γ se_scrut ts.length ts 0 (R := R) (Φ := Φ)
            henv hS_scrut hse_wf
            (fun j hj v ρ' st' se hΨ hse_wf hse_eval => by
              iintro ⟨Hsl, Hv, HR⟩
              iapply (hpost v ρ' st' se hΨ hse_wf hse_eval)
              isplitl [Hsl]
              · iexact Hsl
              · isplitl [Hv]
                · rw [← htys (branches[j]) (List.getElem_mem _)]
                  iexact Hv
                · iexact HR)
            tag htag_branches (by simpa [Nat.zero_add] using heval_tag)
          have hsc_eval : se_scrut.eval ρ_scrut = Runtime.Val.inj tag ts.length v_payload := by
            exact heval_se.trans hval_eq
          have hbranch_entail :
              st_scrut.sl W ρ_scrut ∗
                  TinyML.ValSumRel W tag v_payload ts ∗
                    (S.typed W γg γ ∗ R) ⊢
                wp W.pctx
                  ((Runtime.Expr.subst γ
                        (Runtime.Expr.fix Runtime.Binder.none [branches[tag].1.runtime] branches[tag].2.runtime)).app
                    [Runtime.Expr.val v_payload])
                  Φ := by
            refine BIBase.Entails.trans ?_ (by simpa [Nat.zero_add] using hbranch_wp v_payload ((Nat.zero_add tag).symm ▸ hsc_eval))
            iintro ⟨Hsl, Hsum, #HT, HR⟩
            isplitl [Hsl]
            · simp only [State.sl_eq]
              iexact Hsl
            · isplitl [Hsum]
              · iapply (TinyML.ValSumRel.of_getElem? (W := W) hget)
                iexact Hsum
              · iframe HT HR
          have hmatch_entail :
              st_scrut.sl W ρ_scrut ∗
                  TinyML.ValSumRel W tag v_payload ts ∗
                    (S.typed W γg γ ∗ R) ⊢
                wp W.pctx
                  ((Runtime.Expr.val (Runtime.Val.inj tag ts.length v_payload)).match_
                    (List.map (Runtime.Expr.subst γ ∘ fun p =>
                      Runtime.Expr.fix Runtime.Binder.none [p.1.runtime] p.2.runtime) branches))
                  Φ :=
            PrimitiveLaws.wp_match
              (R := st_scrut.sl W ρ_scrut ∗
                  TinyML.ValSumRel W tag v_payload ts ∗
                    (S.typed W γg γ ∗ R))
              (branch :=
                Runtime.Expr.subst γ
                  (Runtime.Expr.fix Runtime.Binder.none [branches[tag].1.runtime] branches[tag].2.runtime))
              (by simpa [Runtime.Expr.subst_fix] using hbranch_entail)
              (by simp [htag_branches])
              (by simpa using hlen)
          rw [hval_eq]
          iapply hmatch_entail
          iframe Hsl Hsum HT HR)
      · have hΨ_bad : (VerifM.fatal "match branch type annotation mismatch").eval st_scrut ρ_scrut Ψ := by
          simpa [if_pos hlen, if_neg htys] using hΨ_scrut
        exact (VerifM.eval_fatal hΨ_bad).elim

theorem compileBranch_correct (binder : Binder) (body : Expr)
    (ihBody : correctExpr body) :
    correctBranch (binder, body) := by
  intro env W S γg γ sc n i ty_i st ρ Ψ R Φ henv hS hsc_wf heval hpost payload hsc_eval
  simp only [compileBranch] at heval
  by_cases hty : binder.ty = ty_i
  · have hexpect := VerifM.eval_bind heval
    obtain ⟨_, hcont⟩ := VerifM.eval_expectEq hexpect
    have heval_decl := VerifM.eval_bind hcont
    have hdecl := VerifM.eval_decl heval_decl
    let hint := binder.name
    let xv := State.freshConst hint .value st
    have heval_inst := hdecl payload
    have heval_assume := VerifM.eval_bind heval_inst
    have hassume := VerifM.eval_assumePure heval_assume
    let st₁ : State := { decls := st.decls.addConst xv, asserts := st.asserts, owns := st.owns }
    let ρ₁ := ρ.updateConst .value xv.name payload
    have hxv_fresh : xv.name ∉ st.decls.allNames :=
      State.freshConst_fresh st hint .value
    have hstwf : st.decls.wf := (VerifM.eval.wf heval_decl).namesDisjoint
    have hxv_wf : (Term.const (.uninterpreted xv.name .value)).wfIn st₁.decls :=
      by
        simpa [st₁] using
          (Term.const_wfIn_addConst_of_fresh (Δ := st.decls) (c := xv) hstwf hxv_fresh)
    have hformula_wf : (Formula.eq .value sc
        (.unop (.ofInj i n) (.const (.uninterpreted xv.name .value)))).wfIn st₁.decls := by
      refine ⟨Term.wfIn_mono sc hsc_wf (Signature.Subset.subset_addConst _ _)
        (Signature.wf_addConst hstwf hxv_fresh), trivial, hxv_wf⟩
    have hsc_eval_ρ₁ : sc.eval ρ₁ = sc.eval ρ :=
      Term.eval_agreeOn hsc_wf (Env.agreeOn_symm (Env.agreeOn_update_fresh_const hxv_fresh))
    have hformula_eval : Formula.eval ρ₁
        (Formula.eq .value sc (.unop (.ofInj i n) (.const (.uninterpreted xv.name .value)))) := by
      simp [Formula.eval, Term.eval, UnOp.eval]
      rw [hsc_eval_ρ₁, hsc_eval]
      simp [ρ₁, Env.updateConst]
    have heval_assumeAll := hassume hformula_wf hformula_eval
    have hxv_eval : (Term.const (.uninterpreted xv.name .value)).eval ρ₁ = payload := by
      simp [Term.eval, Const.eval, ρ₁, Env.updateConst]
    have hassume_bind₂ := VerifM.eval_bind heval_assumeAll
    have hinterp_eq : SpatialContext.interp W ρ st.owns ⊢ SpatialContext.interp W ρ₁ st.owns :=
      (SpatialContext.interp_agreeOn W (VerifM.eval.wf heval_decl).ownsWf
        (Env.agreeOn_update_fresh_const hxv_fresh)).1
    have hagreeOn_st : Env.agreeOn st.decls ρ ρ₁ :=
      Env.agreeOn_update_fresh_const hxv_fresh
    -- Extract the type-constraints Prop from the iProp `ValHasType W payload ty_i`
    -- assumption, then dispatch into iproof mode to build the final entailment.
    istart
    iintro ⟨Howns, Hpay, #HT, HR⟩
    iintuitionistic Hpay
    ihave Hcheck := TinyML.typeConstraints_hold (ty := ty_i)
        (t := Term.const (.uninterpreted xv.name .value))
        (ρ := ρ₁) (W := W) (v := payload) hxv_eval $$ Hpay
    ipure Hcheck
    obtain ⟨st₂, hst₂_decls, hst₂_owns, _, heval_body'⟩ := VerifM.eval_assumeAll hassume_bind₂
      (fun φ hφ => TinyML.typeConstraints_wfIn hxv_wf φ hφ)
      (fun φ hφ => Hcheck φ hφ)
    have hst₂_owns_eq : st₂.owns = st.owns := hst₂_owns
    have hS₁ := (Scope.wfIn_mono hS (hst₂_decls ▸ Signature.Subset.subset_addConst st.decls xv)
      hagreeOn_st (VerifM.eval.wf heval_body').namesDisjoint).bindRuntimeBinder (b := binder)
      (ty := ty_i) (v := payload) (by rw [hst₂_decls]; exact List.Mem.head _) rfl
      (by simp [ρ₁, xv, hint, Env.updateConst])
    simp only [Runtime.Expr.subst_fix]
    refine PrimitiveLaws.wp_app_lambda_single ?_
    simp only [Runtime.Subst.removeAll'_cons, Runtime.Subst.removeAll'_nil,
      Runtime.Subst.remove'_none]
    rw [Runtime.Expr.subst_remove'_updateBinder]
    refine BIBase.Entails.trans ?_ (ihBody env W _ _ _ henv hS₁ heval_body' hpost)
    istart
    iintro ⟨⟨⟨⟨Howns⟩, #HT⟩, HR⟩, #Hpay⟩
    isplitl [Howns]
    · iapply (show st.sl W ρ ⊢ st₂.sl W ρ₁ by
        simp only [State.sl_eq, hst₂_owns_eq]; exact hinterp_eq)
      iexact Howns
    · isplitl []
      · iapply Scope.typed_bindRuntimeBinder
        iframe # ∗
      · iexact HR
  · have hexpect := VerifM.eval_bind heval
    exact False.elim (hty (VerifM.eval_expectEq hexpect).1)

theorem compileBranchesCons_correct (b : Binder × Expr) (bs : List (Binder × Expr))
    (ihHead : correctBranch b) (ihTail : correctBranches bs) :
    correctBranches (b :: bs) := by
  intro env W S γg γ sc n ts idx st ρ Ψ R Φ henv hS hsc_wf hpost j hj
  cases j with
  | zero =>
    simp only [Nat.add_zero, List.getElem_cons_zero]
    intro heval
    exact ihHead env W S γg γ sc n idx (ts[idx]?.getD .value) henv hS hsc_wf heval
      (by simpa using hpost 0 hj)
  | succ k =>
    have hk : k < bs.length := by simp at hj; omega
    have hidx : idx + (k + 1) = (idx + 1) + k := by omega
    simp only [hidx, List.getElem_cons_succ]
    exact ihTail env W S γg γ sc n ts (idx + 1) henv hS hsc_wf
      (by
        intro j hj' v ρ' st' se hΨ hse_wf hse_eval htyped
        simpa [Nat.add_assoc] using hpost (j + 1) (by simpa using hj') v ρ' st' se hΨ hse_wf hse_eval htyped)
      k hk

theorem compileExprsCons_correct (e : Expr) (rest : List Expr)
    (ihE : correctExpr e) (ihRest : correctExprs rest) :
    correctExprs (e :: rest) := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  simp only [compileExprs] at heval
  simp only [List.map, wps_cons]
  have heval_rest : (compileExprs env S rest).eval st ρ _ := VerifM.eval_bind heval
  refine BIBase.Entails.trans ?_ <|
    ihRest env W S γg γ (R := (S.typed W γg γ ∗ (R))) henv hS (VerifM.eval.decls_grow ρ heval_rest) ?_
  · iintro ⟨Hsl, #HT, HR⟩
    iframe Hsl HT HR
  intro vs ρ_vs st_vs rest_terms hΨ_vs hwf_rest heval_rest
  obtain ⟨hdecls_vs, hagreeOn_vs, hΨ_vs⟩ := hΨ_vs
  have heval_e : (compile env S e).eval st_vs ρ_vs _ := VerifM.eval_bind hΨ_vs
  have hS_vs := Scope.wfIn_mono hS hdecls_vs hagreeOn_vs (VerifM.eval.wf hΨ_vs).namesDisjoint
  refine BIBase.Entails.trans ?_ <|
    ihE env W S γg γ (R := (TinyML.ValsHaveTypes W vs (rest.map Expr.WithTypeVars.ty) ∗ (R))) henv hS_vs (VerifM.eval.decls_grow ρ_vs heval_e) ?_
  · iintro ⟨Hsl, Hvs, #HT, HR⟩
    iframe Hsl HT Hvs HR
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
  have heval_cons : Term.evalList ρ' (se :: rest_terms) (v :: vs) :=
    Term.evalList.cons heval_se
      (Term.evalList_agreeOn
        (fun t ht => hwf_rest t ht)
        hagreeOn_e
        heval_rest)
  exact (by
    iintro ⟨Hsl, Hv, Hvs, HR⟩
    iapply (hpost (v :: vs) ρ' st' (se :: rest_terms) hΨ_e hwf_cons heval_cons)
    isplitl [Hsl]
    · iexact Hsl
    · isplitl [Hv Hvs]
      · iapply (show TinyML.ValHasType W v e.ty ∗
            TinyML.ValsHaveTypes W vs (rest.map Expr.WithTypeVars.ty) ⊢
            TinyML.ValsHaveTypes W (v :: vs) ((e :: rest).map Expr.WithTypeVars.ty) by
          simpa [List.map] using
            (TinyML.ValsHaveTypes.cons W v vs e.ty (rest.map Expr.WithTypeVars.ty)).2)
        iframe Hv Hvs
      · iexact HR)

theorem compileBranchesNil_correct :
    correctBranches [] := by
  intro env W S γg γ sc n ts idx st ρ Ψ R Φ henv hS hsc_wf hpost j hj
  exact absurd hj (Nat.not_lt_zero _)

theorem compileExprsNil_correct :
    correctExprs [] := by
  intro env W S γg γ st ρ Ψ R Φ henv hS heval hpost
  simp only [compileExprs] at heval
  simp only [List.map, wps]
  obtain heval := VerifM.eval_ret heval
  iintro ⟨Hsl, #HT, HR⟩
  iapply (hpost [] ρ st [] heval (by simp) .nil)
  isplitl [Hsl]
  · iexact Hsl
  · isplitl []
    · iapply (show iprop(emp) ⊢ TinyML.ValsHaveTypes W [] ([].map Expr.WithTypeVars.ty) by
        simpa [List.map] using (TinyML.ValsHaveTypes.nil W).2)
      iempintro
    · iexact HR


/-! #### Correctness Theorem -/

mutual
theorem compile_correct (e : Expr) : correctExpr e := by
  cases e with
  | const c =>
    exact compileConst_correct c
  | var x inst vty =>
    exact compileVar_correct x inst vty
  | prim n inst ty =>
    exact compilePrim_correct n inst ty
  | inj tag arity payload ty =>
    exact compileInj_correct tag arity payload ty (compile_correct payload)
  | assert e =>
    exact compileAssert_correct e (compile_correct e)
  | fix self args retTy spec body =>
    exact compileFix_correct self args retTy spec body (compile_correct body)
  | letProd names e body =>
    exact compileLetProd_correct names e body
      (compile_correct e) (compile_correct body)
  | ref ownership e =>
    exact compileRef_correct ownership e (compile_correct e)
  | deref e ty =>
    exact compileDeref_correct e ty (compile_correct e)
  | store loc val =>
    exact compileStore_correct loc val (compile_correct val) (compile_correct loc)
  | arrayMake ownership len init =>
    exact compileArrayMake_correct ownership len init
      (compile_correct len) (compile_correct init)
  | arrayLen arr =>
    exact compileArrayLen_correct arr (compile_correct arr)
  | arrayGet arr idx ty =>
    exact compileArrayGet_correct arr idx ty
      (compile_correct arr) (compile_correct idx)
  | arraySet arr idx val =>
    exact compileArraySet_correct arr idx val
      (compile_correct arr) (compile_correct idx) (compile_correct val)
  | unop op e uty =>
    exact compileUnop_correct op e uty (compile_correct e)
  | binop op l r bty =>
    exact compileBinop_correct op l r bty (compile_correct r) (compile_correct l)
  | letIn mode b e body =>
    cases mode with
    | ghost =>
      exact compileLetInGhost_correct b e body (compile_correct body)
    | runtime =>
      exact compileLetIn_correct b e body
        (compile_correct e) (compile_correct body)
  | ifThenElse cond thn els ty =>
    exact compileIfThenElse_correct cond thn els ty
      (compile_correct cond) (compile_correct thn) (compile_correct els)
  | app fn args gargs aty =>
    exact compileApp_correct fn args gargs aty (compile_correct fn)
      (compileExprs_correct args)
  | tuple es =>
    exact compileTuple_correct es (compileExprs_correct es)
  | match_ scrut branches ty =>
    exact compileMatch_correct scrut branches ty
      (compile_correct scrut) (compileBranches_correct branches)

theorem compileBranches_correct (branches : List (Binder × Expr)) : correctBranches branches := by
  match branches with
  | [] =>
    exact compileBranchesNil_correct
  | (binder, body) :: bs =>
    exact compileBranchesCons_correct (binder, body) bs
      (compileBranch_correct binder body (compile_correct body)) (compileBranches_correct bs)

theorem compileExprs_correct (es : List Expr) : correctExprs es := by
  match es with
  | [] =>
    exact compileExprsNil_correct
  | e :: rest =>
    exact compileExprsCons_correct e rest
      (compile_correct e) (compileExprs_correct rest)
end

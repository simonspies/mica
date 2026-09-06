-- SUMMARY: Compilation of the ghost fragment of TinyML into verifier terms, with entailment correctness proofs.
import Mica.SourceTinyML.Typed
import Mica.Verifier.Compilation
import Mica.Verifier.Bindings
import Mica.Verifier.Specifications

open Iris Iris.BI

variable [MicaGS HasLC.hasLC Sig]
open Typed

/-! ## Ghost Compilation

Ghost code is erased before the program runs, so it takes no step and its
correctness is an entailment rather than a weakest precondition.

That places this layer between the two others. A specification-level term is
pure; a run-time expression is compiled against `wp` and may allocate. A ghost
expression sits in the middle: it moves ownership, through the pre- and
postcondition of every ghost function it calls, but nothing it does can step. -/

/-! ### Definitions -/

mutual
  /-- Compile a ghost expression, returning the term that stands for its value.
  A call of a ghost function asserts the callee's precondition and assumes its
  postcondition, which is what moves ownership.

  Nothing here may take a run-time step, so a closure, an application of
  anything but a ghost function, and every heap operation are rejected rather
  than compiled. `Array.length` is the exception among the array operations: it
  reads no element, so it is a term.

  Bindings go to `G`, never to `B`, and shadowed run-time names are dropped from
  `B`: within ghost code every name is ghost, but the same `G`/`B` split has to
  reach any run-time code the caller continues with. -/
  def compileGhostExpr (Θ : TinyML.TypeEnv) (Δ_spec : Signature)
      (Gf : GhostFns) (G B : Bindings) (Γ : TinyML.TyCtx) :
      Expr → VerifM (Term .value)
    | .const (.int n)  => pure (.unop .ofInt  (.const (.i n)))
    | .const (.bool b) => pure (.unop .ofBool (.const (.b b)))
    | .const (.char c) => pure (.unop .ofChar (.const (.char c)))
    | .const (.string s) => pure (.unop .ofString (.const (.str s)))
    | .const (.float b) => pure (.unop .ofFloat (.const (.fp b)))
    | .const .unit     => pure (Term.const .unit)
    | .var x inst vty => do
        let x' ← match G.lookup x, B.lookup x, Gf.lookup x with
          | some c, _, _ => pure c
          | none, some c, _ => pure c
          | none, none, some _ => VerifM.fatal s!"ghost function used as a value: {x}"
          | none, none, none => VerifM.fatal s!"undefined variable: {x}"
        VerifM.expectEq s!"type annotation mismatch for variable: {x}"
          (((Γ x).map (·.instantiate (TinyML.Typ.ofInst inst))).getD .value) vty
        pure (.const (.uninterpreted x'.name .value))
    | .unop op e uty => do
        let se ← compileGhostExpr Θ Δ_spec Gf G B Γ e
        let ty ← VerifM.expectSome
          s!"type error: operator {repr op} cannot be applied to {repr e.ty}"
          (TinyML.UnOp.typeOf op e.ty)
        VerifM.expectEq "unop type annotation mismatch" ty uty
        VerifM.expectSome s!"unsupported unary operator: {repr op}" (compileUnop op se)
    | .assert e => do
        let se ← compileGhostExpr Θ Δ_spec Gf G B Γ e
        VerifM.assert (Formula.eq .bool (Term.unop .toBool se) (Term.const (.b true)))
        pure (Term.const .unit)
    | .binop op l r bty => do
        let sr ← compileGhostExpr Θ Δ_spec Gf G B Γ r
        let sl ← compileGhostExpr Θ Δ_spec Gf G B Γ l
        let ty ← VerifM.expectSome
          s!"type error: operator {repr op} cannot be applied to {repr l.ty} and {repr r.ty}"
          (TinyML.BinOp.typeOf op l.ty r.ty)
        VerifM.expectEq "binop type annotation mismatch" ty bty
        if op = .div ∨ op = .mod then do
          let i t := Term.unop UnOp.toInt t
          let fol_op := if op == .div then BinOp.div else BinOp.mod
          VerifM.assert (.not (.eq .int (i sr) (.const (.i 0))))
          pure (Term.unop .ofInt (Term.binop fol_op (i sl) (i sr)))
        else
          VerifM.expectSome s!"unsupported binary operator: {repr op}" (compileOp op sl sr)
    | .letIn _ b e body => do
        let se ← compileGhostExpr Θ Δ_spec Gf G B Γ e
        VerifM.expectEq "ghost let type annotation mismatch" b.ty e.ty
        match b.name with
        | none => compileGhostExpr Θ Δ_spec Gf G B Γ body
        | some x =>
          let x' ← VerifM.decl (some x) .value
          VerifM.assume (.pure (Formula.eq .value (.const (.uninterpreted x'.name .value)) se))
          compileGhostExpr Θ Δ_spec Gf ((x, x') :: G) (B.remove x) (Γ.extend x e.ty) body
    | .letProd names e body => do
        let se ← compileGhostExpr Θ Δ_spec Gf G B Γ e
        let tys ← match e.ty with
          | .tuple tys => pure tys
          | _ => VerifM.fatal "letProd expected tuple type"
        let (G', Γ') ← compileProductBinders G Γ names tys se
        compileGhostExpr Θ Δ_spec Gf G' (B.removeBinders names) Γ' body
    | .ifThenElse cond thn els ty => do
        let sc ← compileGhostExpr Θ Δ_spec Gf G B Γ cond
        VerifM.expectEq "if condition type mismatch" cond.ty .bool
        VerifM.expectEq "if branch type annotation mismatch" thn.ty ty
        VerifM.expectEq "if branch type annotation mismatch" els.ty ty
        let branch ← VerifM.all [true, false]
        if branch then do
          VerifM.assume (.pure (.not sc.isFalse))
          compileGhostExpr Θ Δ_spec Gf G B Γ thn
        else do
          VerifM.assume (.pure sc.isFalse)
          compileGhostExpr Θ Δ_spec Gf G B Γ els
    | .app (.var f _ _) args gargs aty =>
      match Gf.lookup f with
      | some (.arrow argTys retTy (some s)) =>
        match Spec.checkWf s Δ_spec with
        | .error msg => VerifM.fatal msg
        | .ok () => do
          VerifM.expectEq "ghost call type annotation mismatch" retTy aty
          VerifM.expectEq "specification arity mismatch" s.args.length argTys.length
          let sterms ← compileGhostExprs Θ Δ_spec Gf G B Γ args
          let gterms ← compileGhostExprs Θ Δ_spec Gf G B Γ gargs
          let (_, result) ← Spec.call (FiniteSubst.base Δ_spec) argTys retTy s
            ((args.map Expr.WithTypeVars.ty).zip sterms)
            ((gargs.map Expr.WithTypeVars.ty).zip gterms)
          pure result
      | _ => VerifM.fatal s!"a ghost expression cannot call `{f}`: it is not a ghost function"
    | .app .. => VerifM.fatal "a ghost expression can only call a ghost function"
    | .prim n _ _ => VerifM.fatal s!"primitive `{n}` must be applied"
    | .tuple es => do
        let terms ← compileGhostExprs Θ Δ_spec Gf G B Γ es
        pure (.unop .ofValList (Terms.toValList terms))
    | .inj tag arity payload ty => do
        match injComponents? Θ ty tag arity payload.ty with
        | some _ => do
            let s ← compileGhostExpr Θ Δ_spec Gf G B Γ payload
            pure (.unop (.ofInj tag arity) s)
        | none => VerifM.fatal "injection type annotation mismatch"
    | .match_ scrut branches ty => do
        let sc ← compileGhostExpr Θ Δ_spec Gf G B Γ scrut
        match sumComponents? Θ scrut.ty with
        | some ts =>
          if ts.length ≠ branches.length then VerifM.fatal "match arity mismatch"
          else if ∀ br ∈ branches, br.2.ty = ty then do
            let actions := compileGhostBranches Θ Δ_spec Gf G B Γ sc ts branches 0
            let i ← VerifM.all (List.range actions.length)
            match actions[i]? with
            | some m => m
            | none => VerifM.fatal "match branch index out of range"
          else
            VerifM.fatal "match branch type annotation mismatch"
        | none => VerifM.fatal "match on non-sum type"
    | .ref .. => VerifM.fatal "a ghost expression cannot allocate"
    | .deref .. => VerifM.fatal "a ghost expression cannot read the heap"
    | .store .. => VerifM.fatal "a ghost expression cannot write the heap"
    | .arrayMake .. => VerifM.fatal "a ghost expression cannot allocate"
    | .arrayLen arr => do
        match arr.ty with
        | .array _ | .ownedArray _ =>
            let sa ← compileGhostExpr Θ Δ_spec Gf G B Γ arr
            pure (.unop .ofInt (.unop .arrayLen sa))
        | _ => VerifM.fatal "Array.length operand is not an array"
    | .arrayGet .. => VerifM.fatal "a ghost expression cannot read the heap"
    | .arraySet .. => VerifM.fatal "a ghost expression cannot write the heap"
    | .fix .. => VerifM.fatal "a ghost expression cannot build a closure"

  /-- Assume the scrutinee is `ofInj i n payload`, then compile the branch. -/
  def compileGhostBranch (Θ : TinyML.TypeEnv) (Δ_spec : Signature)
      (Gf : GhostFns) (G B : Bindings) (Γ : TinyML.TyCtx)
      (sc : Term .value) (n : Nat) (i : Nat) (ty_i : TinyML.Typ)
      : Binder × Expr → VerifM (Term .value)
    | (binder, body) => do
        VerifM.expectEq "match binder type annotation mismatch" binder.ty ty_i
        let xv ← VerifM.decl binder.name .value
        VerifM.assume (.pure (.eq .value sc (.unop (.ofInj i n) (.const (.uninterpreted xv.name .value)))))
        VerifM.assumeAll (TinyML.typeConstraints ty_i (.const (.uninterpreted xv.name .value)))
        match binder.name with
        | some x =>
          compileGhostExpr Θ Δ_spec Gf ((x, xv) :: G) (B.remove x)
            (Γ.extendBinder binder ty_i) body
        | none =>
          compileGhostExpr Θ Δ_spec Gf G B (Γ.extendBinder binder ty_i) body

  def compileGhostBranches (Θ : TinyML.TypeEnv) (Δ_spec : Signature)
      (Gf : GhostFns) (G B : Bindings) (Γ : TinyML.TyCtx)
      (sc : Term .value) (ts : List TinyML.Typ) :
      List (Binder × Expr) → Nat → List (VerifM (Term .value))
    | [], _ => []
    | branch :: rest, i =>
      compileGhostBranch Θ Δ_spec Gf G B Γ sc ts.length i (ts[i]?.getD .value) branch ::
        compileGhostBranches Θ Δ_spec Gf G B Γ sc ts rest (i + 1)

  def compileGhostExprs (Θ : TinyML.TypeEnv) (Δ_spec : Signature)
      (Gf : GhostFns) (G B : Bindings) (Γ : TinyML.TyCtx) :
      List Expr → VerifM (List (Term .value))
    | [] => pure []
    | e :: es => do
      let rest ← compileGhostExprs Θ Δ_spec Gf G B Γ es
      let se ← compileGhostExpr Θ Δ_spec Gf G B Γ e
      pure (se :: rest)
end



/-! ### Correctness -/

/-! #### Correctness Statements -/

/-- The entailment compiling a ghost expression establishes: it takes the state
to an obligation held against the value the expression denotes, and that value
has the type the expression carries.

Ghost code substitutes into nothing, so `γg` and `γ` are only read here, through
`Bindings.valHasType_of_typedSubst`. Stating the scope's typing that way rather
than over `ρ` is what lets a list of ghost expressions carry it from one element
to the next: `typedScope` does not mention `ρ`, so it survives the state the
previous element moved to. -/
def correctGhostExpr (W : TinyML.World)
    (Gf : GhostFns) (e : Expr) : Prop :=
  ∀ (G B : Bindings) (Γ : TinyML.TyCtx) (γg γ : Runtime.Subst)
    {st : TransState} {ρ : Env}
    {Ψ : Term .value → TransState → Env → Prop} {R : iProp} {Φ : Runtime.Val → iProp},
  W.agrees st.decls ρ →
  G.agreeOnLinked ρ γg →
  G.wfIn st.decls →
  B.agreeOnLinked ρ γ →
  B.wfIn st.decls →
  VerifM.eval (compileGhostExpr W.Θ W.Δ_spec Gf G B Γ e) st ρ Ψ →
  (∀ v st' ρ' t, Ψ t st' ρ' → t.wfIn st'.decls → Term.eval ρ' t = v →
    st'.sl W ρ' ∗ TinyML.ValHasType W v e.ty ∗ R ⊢ Φ v) →
  st.sl W ρ ∗ (Bindings.typedScope W G B Γ γg γ ∗ R) ⊢ |==> ∃ v, Φ v

/-- The same statement for one branch of a `match`, compiled under the
assumption that the scrutinee is the injection the branch stands for. The
payload is typed by the component type the branch binds. -/
def correctGhostBranch (W : TinyML.World)
    (Gf : GhostFns) (branch : Binder × Expr) : Prop :=
  ∀ (G B : Bindings) (Γ : TinyML.TyCtx) (γg γ : Runtime.Subst)
    (sc : Term .value) (n i : Nat) (ty_i : TinyML.Typ)
    {st : TransState} {ρ : Env}
    {Ψ : Term .value → TransState → Env → Prop} {R : iProp} {Φ : Runtime.Val → iProp},
  W.agrees st.decls ρ →
  G.agreeOnLinked ρ γg →
  G.wfIn st.decls →
  B.agreeOnLinked ρ γ →
  B.wfIn st.decls →
  sc.wfIn st.decls →
  VerifM.eval (compileGhostBranch W.Θ W.Δ_spec Gf G B Γ sc n i ty_i branch) st ρ Ψ →
  (∀ v st' ρ' t, Ψ t st' ρ' → t.wfIn st'.decls → Term.eval ρ' t = v →
    st'.sl W ρ' ∗ TinyML.ValHasType W v branch.2.ty ∗ R ⊢ Φ v) →
  ∀ payload, sc.eval ρ = Runtime.Val.inj i n payload →
    st.sl W ρ ∗ TinyML.ValHasType W payload ty_i ∗
      (Bindings.typedScope W G B Γ γg γ ∗ R) ⊢ |==> ∃ v, Φ v

/-- The same statement for the whole branch list: `j` is the branch the case
split picked, counted from `idx`, and the postcondition types it. -/
def correctGhostBranches (W : TinyML.World)
    (Gf : GhostFns) (branches : List (Binder × Expr)) : Prop :=
  ∀ (G B : Bindings) (Γ : TinyML.TyCtx) (γg γ : Runtime.Subst)
    (sc : Term .value) (n : Nat) (ts : List TinyML.Typ) (idx : Nat)
    {st : TransState} {ρ : Env}
    {Ψ : Term .value → TransState → Env → Prop} {R : iProp} {Φ : Runtime.Val → iProp},
  W.agrees st.decls ρ →
  G.agreeOnLinked ρ γg →
  G.wfIn st.decls →
  B.agreeOnLinked ρ γ →
  B.wfIn st.decls →
  sc.wfIn st.decls →
  (∀ (j : Nat) (hj : j < branches.length) v st' ρ' t, Ψ t st' ρ' → t.wfIn st'.decls →
    Term.eval ρ' t = v →
    st'.sl W ρ' ∗ TinyML.ValHasType W v (branches[j]).2.ty ∗ R ⊢ Φ v) →
  ∀ (j : Nat) (hj : j < branches.length),
    VerifM.eval (compileGhostBranch W.Θ W.Δ_spec Gf G B Γ sc n (idx + j)
      (ts[idx + j]?.getD .value) (branches[j])) st ρ Ψ →
    ∀ payload, sc.eval ρ = Runtime.Val.inj (idx + j) n payload →
      st.sl W ρ ∗ TinyML.ValHasType W payload (ts[idx + j]?.getD .value) ∗
        (Bindings.typedScope W G B Γ γg γ ∗ R) ⊢ |==> ∃ v, Φ v

/-- The same statement over a list, as `compileGhostExprs` compiles one: the
obligations of the elements are chained, and the update each leaves is absorbed
by the next. -/
def correctGhostExprs (W : TinyML.World)
    (Gf : GhostFns) (es : List Expr) : Prop :=
  ∀ (G B : Bindings) (Γ : TinyML.TyCtx) (γg γ : Runtime.Subst)
    {st : TransState} {ρ : Env}
    {Ψ : List (Term .value) → TransState → Env → Prop} {R : iProp}
    {Φ : List Runtime.Val → iProp},
  W.agrees st.decls ρ →
  G.agreeOnLinked ρ γg →
  G.wfIn st.decls →
  B.agreeOnLinked ρ γ →
  B.wfIn st.decls →
  VerifM.eval (compileGhostExprs W.Θ W.Δ_spec Gf G B Γ es) st ρ Ψ →
  (∀ vs st' ρ' ts, Ψ ts st' ρ' → (∀ t ∈ ts, t.wfIn st'.decls) → Terms.Eval ρ' ts vs →
    st'.sl W ρ' ∗ TinyML.ValsHaveTypes W vs (es.map Expr.WithTypeVars.ty) ∗ R ⊢ Φ vs) →
  st.sl W ρ ∗ (Bindings.typedScope W G B Γ γg γ ∗ R) ⊢ |==> ∃ vs, Φ vs


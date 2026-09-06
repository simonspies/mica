-- SUMMARY: Compilation and verification of the ghost fragment: ghost expressions, and ghost declarations with a termination measure.
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

/-- Substitute the actual arguments in the measure, keeping the caller's rank
    fixed. Definedness is part of the obligation, including for `[@@fn]` calls. -/
def GhostFns.Guard.condition (guard : GhostFns.Guard) (Δ : Signature)
    (names : List String) (terms : List (Term .value)) : Formula :=
  let σ := Spec.argSubst Subst.id names terms
  let m := guard.measure.term.subst σ
  .and (guard.measure.defined.subst σ Δ.allNames)
    (.and (.binpred .le (.const (.i 0)) m) (.binpred .lt m guard.rank))

/-- Check a recursive call before its specification can supply a result.
    Completed declarations have no guard. -/
def GhostFns.Entry.check (entry : GhostFns.Entry) (names : List String)
    (terms : List (Term .value)) : VerifM Unit :=
  match entry.guard with
  | none => pure ()
  | some guard => do
    VerifM.expectEq "recursive ghost call measure arity mismatch" terms.length names.length
    let Δ ← VerifM.decls
    let φ := guard.condition Δ names terms
    match φ.checkWf Δ with
    | .error msg => VerifM.fatal msg
    | .ok () => VerifM.assert φ

omit [MicaGS HasLC.hasLC Sig] in
/-- Successful guard checking establishes the instantiated termination
    obligation and leaves the verifier state unchanged. -/
theorem GhostFns.Entry.check_correct {entry : GhostFns.Entry} {names : List String}
    {terms : List (Term .value)} {st : TransState} {ρ : Env}
    {Q : Unit → TransState → Env → Prop}
    (h : VerifM.eval (entry.check names terms) st ρ Q) :
    (∀ guard, entry.guard = some guard →
      terms.length = names.length ∧ (guard.condition st.decls names terms).eval ρ) ∧
      Q () st ρ := by
  simp only [GhostFns.Entry.check] at h
  cases hg : entry.guard with
  | none =>
    simp only [hg] at h
    exact ⟨by simp, VerifM.eval_ret h⟩
  | some guard =>
    simp only [hg] at h
    obtain ⟨hlen, h⟩ := VerifM.eval_bind_expectEq h
    have h := VerifM.eval_decls (VerifM.eval_bind h)
    cases hc : (guard.condition st.decls names terms).checkWf st.decls with
    | error msg => simp only [hc] at h; exact (VerifM.eval_fatal h).elim
    | ok u =>
      cases u
      simp only [hc] at h
      obtain ⟨hφ, hQ⟩ := VerifM.eval_assert h (Formula.checkWf_ok hc)
      exact ⟨by intro guard' heq; cases heq; exact ⟨hlen, hφ⟩, hQ⟩

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
      | some ⟨.arrow argTys retTy (some s), guard⟩ =>
        match Spec.checkWf s Δ_spec with
        | .error msg => VerifM.fatal msg
        | .ok () => do
          VerifM.expectEq "ghost call type annotation mismatch" retTy aty
          VerifM.expectEq "specification arity mismatch" s.args.length argTys.length
          let sterms ← compileGhostExprs Θ Δ_spec Gf G B Γ args
          let gterms ← compileGhostExprs Θ Δ_spec Gf G B Γ gargs
          GhostFns.Entry.check ⟨.arrow argTys retTy (some s), guard⟩ s.allArgs (sterms ++ gterms)
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

/-! ### Helper lemmas -/

omit [MicaGS HasLC.hasLC Sig] in
theorem compileGhostBranches_length_get (Θ : TinyML.TypeEnv) (Δ_spec : Signature)
    (Gf : GhostFns) (G B : Bindings) (Γ : TinyML.TyCtx)
    (sc : Term .value) (ts : List TinyML.Typ)
    (branches : List (Binder × Expr)) (idx : Nat) :
    (compileGhostBranches Θ Δ_spec Gf G B Γ sc ts branches idx).length = branches.length ∧
    ∀ j, j < branches.length →
      (compileGhostBranches Θ Δ_spec Gf G B Γ sc ts branches idx)[j]? =
        branches[j]?.map (fun branch =>
          compileGhostBranch Θ Δ_spec Gf G B Γ sc ts.length (idx + j)
            (ts[idx + j]?.getD .value) branch) := by
  induction branches generalizing idx with
  | nil => exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | cons b bs ih =>
    have ⟨ih_len, ih_get⟩ := ih (idx + 1)
    constructor
    · simp [compileGhostBranches, ih_len]
    · intro j hj
      cases j with
      | zero => simp [compileGhostBranches]
      | succ k =>
        simp [compileGhostBranches]
        have hk : k < bs.length := Nat.lt_of_succ_lt_succ hj
        have : idx + 1 + k = idx + (k + 1) := by omega
        rw [ih_get k hk, this]


/-! ### Correctness -/

/-! #### Correctness Statements -/

/-- The entailment compiling a ghost expression establishes: it takes the state
to an obligation held against the value the expression denotes, and that value
has the type the expression carries.

`typedScope` does not mention `ρ`, so a list of ghost expressions carries the
scope's typing from one element to the next, across the state each moved to. -/
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
  GhostFns.wellTyped W st.decls ρ Gf →
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
  GhostFns.wellTyped W st.decls ρ Gf →
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
  GhostFns.wellTyped W st.decls ρ Gf →
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
  GhostFns.wellTyped W st.decls ρ Gf →
  VerifM.eval (compileGhostExprs W.Θ W.Δ_spec Gf G B Γ es) st ρ Ψ →
  (∀ vs st' ρ' ts, Ψ ts st' ρ' → (∀ t ∈ ts, t.wfIn st'.decls) → Terms.Eval ρ' ts vs →
    st'.sl W ρ' ∗ TinyML.ValsHaveTypes W vs (es.map Expr.WithTypeVars.ty) ∗ R ⊢ Φ vs) →
  st.sl W ρ ∗ (Bindings.typedScope W G B Γ γg γ ∗ R) ⊢ |==> ∃ vs, Φ vs

/-! #### Correctness Compatibility Lemmas -/

omit [MicaGS HasLC.hasLC Sig] in
/-- Discard the value a ghost step produces: what follows it is stated without
mentioning that value. -/
private theorem bupd_forget {α : Type} {P Q : iProp}
    (h : P ⊢ |==> ∃ _ : α, Q) : P ⊢ |==> Q :=
  h.trans (bupd_mono (exists_elim fun _ => .rfl))

omit [MicaGS HasLC.hasLC Sig] in
/-- Chain two ghost steps: the update the first one leaves is absorbed by the
second, which is itself an update. -/
private theorem bupd_absorb {α : Type} {P Q : iProp}
    (h : P ⊢ |==> ∃ _ : α, |==> Q) : P ⊢ |==> Q :=
  (bupd_forget h).trans bupd_trans

/-- A construct the ghost layer rejects: nothing compiles, so there is nothing
to prove. -/
theorem compileGhostRejected_correct (W : TinyML.World) (Gf : GhostFns) (e : Expr)
    (hfatal : ∀ (Θ : TinyML.TypeEnv) (Δ_spec : Signature) (G B : Bindings) (Γ : TinyML.TyCtx),
      ∃ msg, compileGhostExpr Θ Δ_spec Gf G B Γ e = VerifM.fatal msg) :
    correctGhostExpr W Gf e := by
  intro G B Γ _γg _γ _st _ρ _Ψ _R _Φ _hag _hgagree _hgwf _hagree _hbwf _hGf heval _hpost
  obtain ⟨msg, hmsg⟩ := hfatal W.Θ W.Δ_spec G B Γ
  rw [hmsg] at heval
  exact (VerifM.eval_fatal heval).elim

theorem compileGhostConst_correct (W : TinyML.World) (Gf : GhostFns) (c : TinyML.Const) :
    correctGhostExpr W Gf (.const c) := by
  intro G B Γ γg γ st ρ Ψ R Φ _hag _hgagree _hgwf _hagree _hbwf _hGf heval hpost
  -- Every constant denotes a value in the state it is compiled in, so the
  -- obligation is discharged without an update.
  have step : ∀ (ty : TinyML.Typ) (v : Runtime.Val) (t : Term .value),
      (∀ v st' ρ' t, Ψ t st' ρ' → t.wfIn st'.decls → Term.eval ρ' t = v →
        st'.sl W ρ' ∗ TinyML.ValHasType W v ty ∗ R ⊢ Φ v) →
      Ψ t st ρ → t.wfIn st.decls → Term.eval ρ t = v → (⊢ TinyML.ValHasType W v ty) →
      st.sl W ρ ∗ (Bindings.typedScope W G B Γ γg γ ∗ R) ⊢ |==> ∃ v, Φ v := by
    intro ty v t hpost hΨ hwft hev hval
    refine BIBase.Entails.trans ?_ bupd_intro
    istart
    iintro ⟨Howns, -, HR⟩
    iexists v
    iapply (hpost v st ρ t hΨ hwft hev)
    iframe
    exact hval
  cases c <;>
    simp only [compileGhostExpr] at heval <;>
    simp only [Expr.WithTypeVars.ty, Const.ty] at hpost
  case int n =>
    exact step _ (.int n) _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.denote]) (TinyML.ValHasType.int_intro W n)
  case bool b =>
    exact step _ (.bool b) _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.denote]) (TinyML.ValHasType.bool_intro W b)
  case char c =>
    exact step _ (.char c) _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.denote]) (TinyML.ValHasType.char_intro W c)
  case string s =>
    exact step _ (.str s) _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.denote]) (TinyML.ValHasType.string_intro W s)
  case float b =>
    exact step _ (.float b) _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
      (by simp [Term.eval, UnOp.eval, Const.denote]) (TinyML.ValHasType.float_intro W b)
  case unit =>
    exact step _ .unit _ hpost (VerifM.eval_ret heval)
      (by simp [Term.wfIn, Const.wfIn]) (by simp [Term.eval]) (TinyML.ValHasType.unit_intro W)

theorem compileGhostVar_correct (W : TinyML.World) (Gf : GhostFns) (x : String)
    (inst : List (TinyML.TyVar × TinyML.Typ)) (vty : TinyML.Typ) :
    correctGhostExpr W Gf (.var x inst vty) := by
  intro G B Γ γg γ st ρ Ψ R Φ _hag hgagree hgwf hagree hbwf hGf heval hpost
  simp only [compileGhostExpr] at heval
  -- A ghost name shadows a run-time one, so the ghost bindings are read first.
  obtain ⟨x', hbind, heval⟩ : ∃ x', (G.lookup x = some x' ∨ B.lookup x = some x') ∧
      VerifM.eval (do
        VerifM.expectEq s!"type annotation mismatch for variable: {x}"
          (((Γ x).map (·.instantiate (TinyML.Typ.ofInst inst))).getD .value) vty
        pure (Term.const (.uninterpreted x'.name .value))) st ρ Ψ := by
    cases hg : G.lookup x with
    | some c =>
      simp only [hg] at heval
      exact ⟨c, Or.inl rfl, VerifM.eval_ret (VerifM.eval_bind heval)⟩
    | none =>
      cases hb : B.lookup x with
      | some c =>
        simp only [hg, hb] at heval
        exact ⟨c, Or.inr rfl, VerifM.eval_ret (VerifM.eval_bind heval)⟩
      | none =>
        cases hgf : Gf.lookup x with
        | some _ =>
          simp only [hg, hb, hgf] at heval
          exact (VerifM.eval_fatal (VerifM.eval_bind heval)).elim
        | none =>
          simp only [hg, hb, hgf] at heval
          exact (VerifM.eval_fatal (VerifM.eval_bind heval)).elim
  obtain ⟨hcheck, hcont⟩ := VerifM.eval_bind_expectEq heval
  simp only [Expr.WithTypeVars.ty] at hpost
  have hsort : x'.sort = .value := by
    rcases hbind with hb | hb
    · exact (hgagree x x' hb).1
    · exact (hagree x x' hb).1
  have hconst : x' ∈ st.decls.consts := by
    rcases hbind with hb | hb
    · obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hb
      exact hgwf (x, x') (by rw [heq]; simp)
    · obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hb
      exact hbwf (x, x') (by rw [heq]; simp)
  have hwfst : st.decls.wf := (VerifM.eval.wf heval).namesDisjoint
  have hΨ : Ψ (Term.const (.uninterpreted x'.name .value)) st ρ := VerifM.eval_ret hcont
  have hwfv : (Term.const (.uninterpreted x'.name .value)).wfIn st.decls := by
    cases x' with
    | mk n s =>
      simp only at hsort; subst hsort
      exact Term.const_wfIn_of_mem hwfst hconst
  have hteval : Term.eval ρ (Term.const (.uninterpreted x'.name .value))
      = ρ.consts .value x'.name := by
    simp [Term.eval, Const.denote]
  have htyped : Bindings.typedScope W G B Γ γg γ ⊢
      TinyML.ValHasType W (ρ.consts .value x'.name) vty := by
    cases hΓx : Γ x with
    | none =>
      have hvty : vty = .value := by simpa [hΓx] using hcheck.symm
      subst hvty
      refine true_intro.trans ?_
      iapply (TinyML.ValHasType.value W (ρ.consts .value x'.name)).2
    | some u =>
      have htv : u.instantiate (TinyML.Typ.ofInst inst) = vty := by simpa [hΓx] using hcheck
      rw [← htv]
      exact Bindings.typedScope_valHasType W (TinyML.Typ.ofInst inst) hgagree hagree hbind hΓx
  refine BIBase.Entails.trans ?_ bupd_intro
  istart
  iintro ⟨Howns, #HT, HR⟩
  iexists (ρ.consts .value x'.name)
  iapply (hpost (ρ.consts .value x'.name) st ρ _ hΨ hwfv hteval)
  isplitl [Howns]
  · iexact Howns
  · isplitl []
    · iapply htyped
      iexact HT
    · iexact HR

theorem compileGhostUnop_correct (W : TinyML.World) (Gf : GhostFns)
    (op : TinyML.UnOp) (e : Expr) (uty : TinyML.Typ)
    (ih : correctGhostExpr W Gf e) :
    correctGhostExpr W Gf (.unop op e uty) := by
  intro G B Γ γg γ st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf heval hpost
  simp only [compileGhostExpr] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  have heval_e := VerifM.eval_bind heval
  refine bupd_forget (ih G B Γ γg γ (R := R) (Φ := fun _ => iprop(∃ v, Φ v))
    hag hgagree hgwf hagree hbwf hGf (VerifM.eval.decls_grow ρ heval_e) ?_)
  intro v_e st₁ ρ_e se hΨ_e hse_wf heval_se
  obtain ⟨_, _, hΨ_e⟩ := hΨ_e
  obtain ⟨ty, htypeOf, hΨ_e⟩ := VerifM.eval_bind_expectSome hΨ_e
  obtain ⟨hty_eq, hΨ_e⟩ := VerifM.eval_bind_expectEq hΨ_e
  obtain ⟨t, hcompUnop, hΨ_e⟩ := VerifM.eval_expectSome hΨ_e
  have htyped :
      st₁.sl W ρ_e ∗ TinyML.ValHasType W v_e e.ty ∗ R ⊢
        st₁.sl W ρ_e ∗
          iprop(∃ w, ⌜TinyML.evalUnOp op v_e = some w⌝ ∗ TinyML.ValHasType W w ty) ∗ R :=
    sep_mono_right (sep_mono_left (TinyML.evalUnOp_typed htypeOf))
  refine htyped.trans ?_
  istart
  iintro ⟨Howns, Hex, HR⟩
  icases Hex with ⟨%w, %heval_op, Hwty⟩
  have ht_eval : t.eval ρ_e = w := compileUnop_eval heval_se heval_op hcompUnop
  iexists w
  iapply (show st₁.sl W ρ_e ∗ TinyML.ValHasType W w ty ∗ R ⊢ Φ w by
    simpa [hty_eq] using hpost w st₁ ρ_e t hΨ_e (compileUnop_wfIn hse_wf hcompUnop) ht_eval)
  isplitl [Howns]
  · iexact Howns
  · isplitl [Hwty]
    · iexact Hwty
    · iexact HR

/-- The step shared by the integer binary operations the compiler guards with an
assertion. `folOp` is the operation the compiled term uses and `g` the integer
operation it must denote. -/
private theorem compileGhostIntBinop_correct (W : TinyML.World) {R : iProp}
    {Φ : Runtime.Val → iProp} {Ψ : Term .value → TransState → Env → Prop}
    {st : TransState} {ρ : Env} {sl sr : Term .value} {vl vr : Runtime.Val}
    (folOp : BinOp .int .int .int) (g : Int → Int → Int)
    (hpost : ∀ v st' ρ' t, Ψ t st' ρ' → t.wfIn st'.decls → Term.eval ρ' t = v →
      st'.sl W ρ' ∗ TinyML.ValHasType W v .int ∗ R ⊢ Φ v)
    (hΨ : Ψ (.unop .ofInt (.binop folOp (.unop .toInt sl) (.unop .toInt sr))) st ρ)
    (hwft : (Term.unop .ofInt
      (.binop folOp (.unop .toInt sl) (.unop .toInt sr))).wfIn st.decls)
    (hterm : ∀ a b : Int, vl = .int a → vr = .int b →
      Term.eval ρ (.unop .ofInt (.binop folOp (.unop .toInt sl) (.unop .toInt sr)))
        = Runtime.Val.int (g a b)) :
    st.sl W ρ ∗ (TinyML.ValHasType W vl .int ∗ (TinyML.ValHasType W vr .int ∗ R)) ⊢
      ∃ v, Φ v := by
  istart
  iintro ⟨Howns, Hvl, Hvr, HR⟩
  ihave Hvl_int := (TinyML.ValHasType.int W vl).1 $$ Hvl
  ihave Hvr_int := (TinyML.ValHasType.int W vr).1 $$ Hvr
  icases Hvl_int with ⟨%a, %hvl⟩
  icases Hvr_int with ⟨%b, %hvr⟩
  iexists (Runtime.Val.int (g a b))
  iapply (hpost (.int (g a b)) st ρ _ hΨ hwft (hterm a b hvl hvr))
  isplitl [Howns]
  · iexact Howns
  · isplitl []
    · exact TinyML.ValHasType.int_intro W (g a b)
    · iexact HR

theorem compileGhostBinop_correct (W : TinyML.World) (Gf : GhostFns)
    (op : TinyML.BinOp) (l r : Expr) (bty : TinyML.Typ)
    (ihR : correctGhostExpr W Gf r) (ihL : correctGhostExpr W Gf l) :
    correctGhostExpr W Gf (.binop op l r bty) := by
  intro G B Γ γg γ st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf heval hpost
  simp only [compileGhostExpr] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  have heval_r := VerifM.eval_bind heval
  refine bupd_absorb (BIBase.Entails.trans (Helpers.ctx_dup W G B Γ st ρ γg γ R)
    (ihR G B Γ γg γ (R := iprop(Bindings.typedScope W G B Γ γg γ ∗ R))
      (Φ := fun _ => iprop(|==> ∃ v, Φ v))
      hag hgagree hgwf hagree hbwf hGf (VerifM.eval.decls_grow ρ heval_r) ?_))
  intro vr st₁ ρ_r sr hΨ_r hsr_wf heval_sr
  obtain ⟨hdecls_r, hagreeOn_r, hΨ_r⟩ := hΨ_r
  have hag_r := hag.step hdecls_r hagreeOn_r
  have hGf_r := hGf.step hdecls_r hagreeOn_r (VerifM.eval.wf hΨ_r).namesDisjoint
  have hagree_r := Bindings.agreeOnLinked_env_agree hagree hagreeOn_r hbwf
  have hgagree_r := Bindings.agreeOnLinked_env_agree hgagree hagreeOn_r hgwf
  have hbwf_r : B.wfIn st₁.decls := fun p hp => hdecls_r.consts _ (hbwf p hp)
  have hgwf_r : G.wfIn st₁.decls := fun p hp => hdecls_r.consts _ (hgwf p hp)
  have heval_l := VerifM.eval_bind hΨ_r
  refine bupd_forget (BIBase.Entails.trans (Helpers.ctx_push W G B Γ st₁ ρ_r γg γ R vr r.ty)
    (ihL G B Γ γg γ (R := iprop(TinyML.ValHasType W vr r.ty ∗ R))
      (Φ := fun _ => iprop(∃ v, Φ v))
      hag_r hgagree_r hgwf_r hagree_r hbwf_r hGf_r (VerifM.eval.decls_grow ρ_r heval_l) ?_))
  intro vl st₂ ρ_l sl hΨ_l hsl_wf heval_sl
  obtain ⟨hdecls_l, hagreeOn_l, hΨ_l⟩ := hΨ_l
  obtain ⟨ty, htypeOf, hΨ_l⟩ := VerifM.eval_bind_expectSome hΨ_l
  obtain ⟨hty_eq, hΨ_l'⟩ := VerifM.eval_bind_expectEq hΨ_l
  have hsr_ρ_l : sr.eval ρ_l = vr := by
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
    obtain ⟨hlty, hrty, hty_int⟩ := TinyML.BinOp.typeOf_arith (by tauto) htypeOf
    have hassert_wf :
        (Formula.not (.eq .int (.unop .toInt sr) (.const (.i 0)))).wfIn st₂.decls := by
      simpa [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn] using
        (Term.wfIn_mono sr hsr_wf hdecls_l (VerifM.eval.wf hΨ_div).namesDisjoint)
    have ⟨_hne_zero, hΨ_post⟩ := VerifM.eval_assert (VerifM.eval_bind hΨ_div) hassert_wf
    obtain hΨ_post := VerifM.eval_ret hΨ_post
    have hbty : bty = .int := hty_eq.symm.trans hty_int
    have hwf_sr_l : sr.wfIn st₂.decls :=
      Term.wfIn_mono sr hsr_wf hdecls_l (VerifM.eval.wf hΨ_div).namesDisjoint
    subst hbty
    rcases hdivmod with rfl | rfl
    · simpa [hlty, hrty] using
        compileGhostIntBinop_correct W BinOp.div (· / ·) hpost (by simpa using hΨ_post)
          (by simpa [Term.wfIn, BinOp.wfIn, UnOp.wfIn] using And.intro hsl_wf hwf_sr_l)
          (by intro a b hvl hvr; subst hvl; subst hvr
              simp [Term.eval, UnOp.eval, BinOp.eval, heval_sl, hsr_ρ_l])
    · simpa [hlty, hrty] using
        compileGhostIntBinop_correct W BinOp.mod (· % ·) hpost (by simpa using hΨ_post)
          (by simpa [Term.wfIn, BinOp.wfIn, UnOp.wfIn] using And.intro hsl_wf hwf_sr_l)
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
        · isplitl [Hvl]
          · iexact Hvl
          · iexact Hvr
        · iexact HR
    have htyped :
        st₂.sl W ρ_l ∗ (TinyML.ValHasType W vl l.ty ∗ (TinyML.ValHasType W vr r.ty ∗ R)) ⊢
          st₂.sl W ρ_l ∗
            iprop(∃ w, ⌜TinyML.evalBinOp op vl vr = some w⌝ ∗ TinyML.ValHasType W w ty) ∗ R :=
      hprep.trans (sep_mono_right (sep_mono_left (TinyML.evalBinOp_typed
        (fun h => hndivmod (Or.inl h)) (fun h => hndivmod (Or.inr h)) htypeOf)))
    have hwfst₂ : st₂.decls.wf := (VerifM.eval.wf hΨ_ndiv).namesDisjoint
    obtain hΨ_ndiv := VerifM.eval_ret hΨ_ndiv
    have hwf_sr_l : sr.wfIn st₂.decls := Term.wfIn_mono sr hsr_wf hdecls_l hwfst₂
    refine htyped.trans ?_
    istart
    iintro ⟨Howns, Hex, HR⟩
    icases Hex with ⟨%w, %heval_op, Hwty⟩
    have ht_eval : t.eval ρ_l = w := compileOp_eval heval_sl hsr_ρ_l heval_op hcompOp
    iexists w
    iapply (show st₂.sl W ρ_l ∗ TinyML.ValHasType W w ty ∗ R ⊢ Φ w by
      simpa [hty_eq] using
        hpost w st₂ ρ_l t hΨ_ndiv (compileOp_wfIn hsl_wf hwf_sr_l hcompOp) ht_eval)
    isplitl [Howns]
    · iexact Howns
    · isplitl [Hwty]
      · iexact Hwty
      · iexact HR

theorem compileGhostAssert_correct (W : TinyML.World) (Gf : GhostFns) (e : Expr)
    (ih : correctGhostExpr W Gf e) :
    correctGhostExpr W Gf (.assert e) := by
  intro G B Γ γg γ st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf heval hpost
  simp only [compileGhostExpr] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  have heval_e := VerifM.eval_bind heval
  refine bupd_forget (ih G B Γ γg γ (R := R) (Φ := fun _ => iprop(∃ v, Φ v))
    hag hgagree hgwf hagree hbwf hGf (VerifM.eval.decls_grow ρ heval_e) ?_)
  intro v_e st₁ ρ_e se hΨ_e hse_wf heval_se
  obtain ⟨_, _, hΨ_e⟩ := hΨ_e
  have hwf_φ : (Formula.eq .bool (Term.unop .toBool se) (Term.const (.b true))).wfIn st₁.decls := by
    simpa [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn] using hse_wf
  obtain ⟨hφ, hcont⟩ := VerifM.eval_assert (VerifM.eval_bind hΨ_e) hwf_φ
  have hΨ_pure := VerifM.eval_ret hcont
  have hvtrue : v_e = .bool true := by
    simp only [Formula.eval, Term.eval, UnOp.eval, Const.denote] at hφ
    rw [heval_se] at hφ
    cases v_e <;> simp_all
  subst hvtrue
  have hprep :
      st₁.sl W ρ_e ∗ TinyML.ValHasType W (.bool true) e.ty ∗ R ⊢
        st₁.sl W ρ_e ∗ TinyML.ValHasType W .unit .unit ∗ R :=
    sep_mono_right (sep_mono_left (true_intro.trans (TinyML.ValHasType.unit_intro W)))
  refine hprep.trans ?_
  refine BIBase.Entails.trans ?_ (exists_intro Runtime.Val.unit)
  exact hpost .unit st₁ ρ_e (Term.const .unit) hΨ_pure trivial (by simp [Term.eval])

theorem compileGhostInj_correct (W : TinyML.World) (Gf : GhostFns)
    (tag arity : Nat) (payload : Expr) (ty : TinyML.Typ)
    (ihPayload : correctGhostExpr W Gf payload) :
    correctGhostExpr W Gf (.inj tag arity payload ty) := by
  intro G B Γ γg γ st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf heval hpost
  simp only [compileGhostExpr] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  cases hcomp : injComponents? W.Θ ty tag arity payload.ty with
  | none =>
    simp [hcomp] at heval
    exact (VerifM.eval_fatal heval).elim
  | some ts =>
    obtain ⟨hty, hlen_ts, hget_ts⟩ := injComponents?_eq hcomp
    simp only [hcomp] at heval
    have heval_p := VerifM.eval_bind heval
    refine bupd_forget (ihPayload G B Γ γg γ (R := R) (Φ := fun _ => iprop(∃ v, Φ v))
      hag hgagree hgwf hagree hbwf hGf (VerifM.eval.decls_grow ρ heval_p) ?_)
    intro v_p st_p ρ_p se_p hΨ_p hse_wf_p heval_se_p
    obtain ⟨_, _, hΨ_p⟩ := hΨ_p
    obtain hΨ_p := VerifM.eval_ret hΨ_p
    have hinj : TinyML.ValHasType W v_p payload.ty ⊢
        TinyML.ValHasType W (.inj tag arity v_p) ty :=
      (TinyML.ValHasType.inj hlen_ts hget_ts).trans (valHasType_sumComponents hty).2
    refine BIBase.Entails.trans (sep_mono_right (sep_mono_left hinj)) ?_
    refine BIBase.Entails.trans ?_ (exists_intro (Runtime.Val.inj tag arity v_p))
    simpa [hlen_ts] using
      hpost (.inj tag arity v_p) st_p ρ_p _ hΨ_p
        (by simp only [Term.wfIn]; exact ⟨trivial, hse_wf_p⟩)
        (by simp [Term.eval, UnOp.eval, heval_se_p])

theorem compileGhostArrayLen_correct (W : TinyML.World) (Gf : GhostFns) (arr : Expr)
    (ihArr : correctGhostExpr W Gf arr) :
    correctGhostExpr W Gf (.arrayLen arr) := by
  cases hty : arr.ty with
  | array elem =>
    intro G B Γ γg γ st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf heval hpost
    simp only [compileGhostExpr, hty] at heval
    simp only [Expr.WithTypeVars.ty] at hpost
    have heval_arr := VerifM.eval_bind heval
    refine bupd_forget (ihArr G B Γ γg γ (R := R) (Φ := fun _ => iprop(∃ v, Φ v))
      hag hgagree hgwf hagree hbwf hGf (VerifM.eval.decls_grow ρ heval_arr) ?_)
    intro v_arr st₁ ρ_arr sa hΨ_arr hsa_wf heval_sa
    obtain ⟨_, _, hΨ_arr⟩ := hΨ_arr
    obtain hret := VerifM.eval_ret hΨ_arr
    rw [hty]
    istart
    iintro ⟨Howns, Harr, HR⟩
    ihave Harr' := (TinyML.ValHasType.array W v_arr elem).1 $$ Harr
    icases Harr' with ⟨%len, %loc, %hv_arr, _⟩
    iexists (Runtime.Val.int len)
    iapply (hpost (.int len) st₁ ρ_arr (.unop .ofInt (.unop .arrayLen sa)) hret
      ⟨trivial, trivial, hsa_wf⟩ (by simp [Term.eval, UnOp.eval, heval_sa, hv_arr]))
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · iapply (TinyML.ValHasType.int_intro W)
      · iexact HR
  | ownedArray elem =>
    intro G B Γ γg γ st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf heval hpost
    simp only [compileGhostExpr, hty] at heval
    simp only [Expr.WithTypeVars.ty] at hpost
    have heval_arr := VerifM.eval_bind heval
    refine bupd_forget (ihArr G B Γ γg γ (R := R) (Φ := fun _ => iprop(∃ v, Φ v))
      hag hgagree hgwf hagree hbwf hGf (VerifM.eval.decls_grow ρ heval_arr) ?_)
    intro v_arr st₁ ρ_arr sa hΨ_arr hsa_wf heval_sa
    obtain ⟨_, _, hΨ_arr⟩ := hΨ_arr
    obtain hret := VerifM.eval_ret hΨ_arr
    rw [hty]
    istart
    iintro ⟨Howns, Harr, HR⟩
    ihave Harr' := (TinyML.ValHasType.ownedArray W v_arr elem).1 $$ Harr
    icases Harr' with ⟨%len, %loc, %hv_arr⟩
    iexists (Runtime.Val.int len)
    iapply (hpost (.int len) st₁ ρ_arr (.unop .ofInt (.unop .arrayLen sa)) hret
      ⟨trivial, trivial, hsa_wf⟩ (by simp [Term.eval, UnOp.eval, heval_sa, hv_arr]))
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · iapply (TinyML.ValHasType.int_intro W)
      · iexact HR
  | prim _ | sum _ | arrow _ _ | ref _ | vec _ | owned _ | empty | value | tuple _ | tvar _
  | named _ _ =>
    intro G B Γ _γg _γ _st _ρ _Ψ _R _Φ _ _ _ _ _ _ heval _
    simp only [compileGhostExpr, hty] at heval
    exact (VerifM.eval_fatal heval).elim

theorem compileGhostTuple_correct (W : TinyML.World) (Gf : GhostFns) (es : List Expr)
    (ihEs : correctGhostExprs W Gf es) :
    correctGhostExpr W Gf (.tuple es) := by
  intro G B Γ γg γ st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf heval hpost
  simp only [compileGhostExpr] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  have heval_es := VerifM.eval_bind heval
  refine bupd_forget (ihEs G B Γ γg γ (R := R) (Φ := fun _ => iprop(∃ v, Φ v))
    hag hgagree hgwf hagree hbwf hGf (VerifM.eval.decls_grow ρ heval_es) ?_)
  intro vs st' ρ' terms hΨ hwf_terms heval_terms
  obtain ⟨_, _, hΨ⟩ := hΨ
  obtain hΨ := VerifM.eval_ret hΨ
  have hstep :
      st'.sl W ρ' ∗ TinyML.ValsHaveTypes W vs (es.map Expr.WithTypeVars.ty) ∗ R ⊢
        st'.sl W ρ' ∗
          TinyML.ValHasType W (.tuple vs) (.tuple (es.map Expr.WithTypeVars.ty)) ∗ R := by
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
  refine hstep.trans ?_
  refine BIBase.Entails.trans ?_ (exists_intro (Runtime.Val.tuple vs))
  exact hpost (Runtime.Val.tuple vs) st' ρ' (.unop .ofValList (Terms.toValList terms)) hΨ
    (by simp only [Term.wfIn]; exact ⟨trivial, Terms.toValList_wfIn hwf_terms⟩)
    (by simp [Term.eval, UnOp.eval, Terms.toValList_eval heval_terms])

theorem compileGhostLetIn_correct (W : TinyML.World) (Gf : GhostFns)
    (mode : TinyML.Mode) (b : Binder) (e body : Expr)
    (ihE : correctGhostExpr W Gf e) (ihBody : correctGhostExpr W Gf body) :
    correctGhostExpr W Gf (.letIn mode b e body) := by
  intro G B Γ γg γ st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf heval hpost
  simp only [compileGhostExpr] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  refine bupd_absorb (BIBase.Entails.trans (Helpers.ctx_dup W G B Γ st ρ γg γ R)
    (ihE G B Γ γg γ (R := iprop(Bindings.typedScope W G B Γ γg γ ∗ R))
      (Φ := fun _ => iprop(|==> ∃ v, Φ v))
      hag hgagree hgwf hagree hbwf hGf (VerifM.eval.decls_grow ρ (VerifM.eval_bind heval)) ?_))
  intro v st₁ ρ₁ t hΨ ht_wf ht_eval
  obtain ⟨hdecls, hagreeOn, hΨ⟩ := hΨ
  obtain ⟨_, hΨ⟩ := VerifM.eval_bind_expectEq hΨ
  have hagree₁ := Bindings.agreeOnLinked_env_agree hagree hagreeOn hbwf
  have hgagree₁ := Bindings.agreeOnLinked_env_agree hgagree hagreeOn hgwf
  have hbwf₁ : B.wfIn st₁.decls := fun p hp => hdecls.consts _ (hbwf p hp)
  have hgwf₁ : G.wfIn st₁.decls := fun p hp => hdecls.consts _ (hgwf p hp)
  have hag₁ := hag.step hdecls hagreeOn
  have hGf₁ := hGf.step hdecls hagreeOn (VerifM.eval.wf hΨ).namesDisjoint
  have hcont : ∀ v st' ρ' t, (fun t st' ρ' =>
        st₁.decls.Subset st'.decls ∧ Env.agreeOn st₁.decls ρ₁ ρ' ∧ Ψ t st' ρ') t st' ρ' →
      t.wfIn st'.decls → Term.eval ρ' t = v →
      st'.sl W ρ' ∗ TinyML.ValHasType W v body.ty ∗ R ⊢ Φ v :=
    fun v st' ρ' t hΨ' hs hw => hpost v st' ρ' t hΨ'.2.2 hs hw
  cases hname : b.name with
  | none =>
    simp [hname] at hΨ
    refine BIBase.Entails.trans ?_ (ihBody G B Γ γg γ (R := R) (Φ := Φ)
      hag₁ hgagree₁ hgwf₁ hagree₁ hbwf₁ hGf₁ (VerifM.eval.decls_grow ρ₁ hΨ) hcont)
    iintro ⟨Howns, _Hv, #HT, HR⟩
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · iexact HT
      · iexact HR
  | some x =>
    simp [hname] at hΨ
    set x' : FOL.Const := ⟨Fresh.freshNumbers x st₁.decls.allNames, .value⟩ with hx'_def
    have hfresh : x'.name ∉ st₁.decls.allNames :=
      Fresh.freshNumbers_not_mem x st₁.decls.allNames
    set st₂ : TransState :=
      { decls := st₁.decls.addConst x',
        asserts := (Formula.eq .value (.const (.uninterpreted x'.name .value)) t) :: st₁.asserts,
        owns := st₁.owns } with hst₂_def
    set ρ₂ := ρ₁.updateConst .value x'.name v with hρ₂_def
    have hagreeOn₂ : Env.agreeOn st₁.decls ρ₁ ρ₂ := Env.agreeOn_update_fresh_const hfresh
    have hΨ_body : (compileGhostExpr W.Θ W.Δ_spec Gf ((x, x') :: G) (B.remove x)
        (Γ.extend x e.ty) body).eval st₂ ρ₂ Ψ := by
      have hdecl := VerifM.eval_decl (VerifM.eval_bind hΨ)
      have h := VerifM.eval_assumePure (VerifM.eval_bind (hdecl v))
      apply h
      · have hstwf : st₁.decls.wf := (VerifM.eval.wf hΨ).namesDisjoint
        simpa [x'] using
          (Formula.eq_wfIn_addConst_of_fresh (Δ := st₁.decls) (c := x') hstwf ht_wf hfresh)
      · simp only [Formula.eval, Term.eval, Const.denote]
        have : v = Term.eval ρ₂ t := by
          rw [Term.eval_env_agree ht_wf (Env.agreeOn_symm hagreeOn₂)]
          exact ht_eval.symm
        simpa [ρ₂, Env.updateConst] using this
    have hρ₂_lookup : ρ₂.consts .value x'.name = v := by simp [ρ₂, Env.updateConst]
    have hρ_agree : Env.agreeOn (Signature.ofConsts (G.map Prod.snd)) ρ₂ ρ₁ := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro y hy; cases hy
      · intro y' hy'
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy'
        exact (hagreeOn₂.2.1 p.2 (hgwf₁ p hp)).symm
      · intro z hz; cases hz
      · intro z hz; cases hz
      · intro z hz; cases hz
      · intro z hz; cases hz
      · intro z hz; cases hz
    have hgagree₂ : Bindings.agreeOnLinked ((x, x') :: G) ρ₂ (Runtime.Subst.update γg x v) := by
      have h := Bindings.agreeOnLinked_cons (B := G) (x := x) (v := x') (γ := γg)
        hgagree₁ hρ_agree (hvty := rfl)
      rwa [hρ₂_lookup] at h
    have hagree₂ : Bindings.agreeOnLinked (B.remove x) ρ₂ γ :=
      Bindings.agreeOnLinked_remove
        (Bindings.agreeOnLinked_env_agree hagree₁ hagreeOn₂ hbwf₁) x
    have hgwf₂ : Bindings.wfIn ((x, x') :: G) st₂.decls := Bindings.wfIn_cons hgwf₁
    have hbwf₂ : Bindings.wfIn (B.remove x) st₂.decls := fun p hp =>
      (Signature.Subset.subset_addConst st₁.decls x').consts _
        (hbwf₁ p (Bindings.mem_of_mem_remove hp))
    have hag₂ := hag₁.step (Signature.Subset.subset_addConst st₁.decls x') hagreeOn₂
    have hGf₂ := hGf₁.step (Signature.Subset.subset_addConst st₁.decls x') hagreeOn₂
      (VerifM.eval.wf hΨ_body).namesDisjoint
    refine BIBase.Entails.trans ?_ (ihBody ((x, x') :: G) (B.remove x) (Γ.extend x e.ty)
      (Runtime.Subst.update γg x v) γ (R := R) (Φ := Φ)
      hag₂ hgagree₂ hgwf₂ hagree₂ hbwf₂ hGf₂ (VerifM.eval.decls_grow ρ₂ hΨ_body)
      (fun v ρ' st' se hΨ' hs hw =>
        hcont v ρ' st' se
          ⟨(Signature.Subset.subset_addConst st₁.decls x').trans hΨ'.1,
            Env.agreeOn_trans hagreeOn₂ (Env.agreeOn_mono
              (Signature.Subset.subset_addConst st₁.decls x') hΨ'.2.1),
            hΨ'.2.2⟩ hs hw))
    have hinterp_eq : SpatialContext.interp W ρ₁ st₁.owns ⊢
        SpatialContext.interp W ρ₂ st₁.owns :=
      (SpatialContext.interp_env_agree W (VerifM.eval.wf hΨ).ownsWf hagreeOn₂).1
    iintro ⟨Howns, Hv, #HT, HR⟩
    isplitl [Howns]
    · simp only [TransState.sl_eq]
      iapply hinterp_eq
      iexact Howns
    · isplitl [Hv]
      · iapply (Bindings.typedScope_cons_ghost (W := W) (G := G) (B := B) (Γ := Γ)
          (γg := γg) (γ := γ) (x := x) (v := x') (te := e.ty) (w := v))
        · iexact HT
        · iexact Hv
      · iexact HR

/-- The binders of a ghost `let` over a tuple: each name joins the ghost scope
at the component type, and the run-time reading of a shadowed name is dropped. -/
theorem compileGhostProductBindersFrom_correct (W : TinyML.World) (Gf : GhostFns)
    (body : Expr) (ihBody : correctGhostExpr W Gf body) :
    ∀ (names : List Binder) (tys : List TinyML.Typ) (tl : Term .vallist)
      (vals : List Runtime.Val) (G B : Bindings) (Γ : TinyML.TyCtx)
      (γg γ : Runtime.Subst) (st : TransState) (ρ : Env)
      (Ψ : Term .value → TransState → Env → Prop) (R : iProp) (Φ : Runtime.Val → iProp),
      VerifM.eval (compileProductBindersFrom G Γ names tys tl) st ρ
        (fun p st' ρ' =>
          (compileGhostExpr W.Θ W.Δ_spec Gf p.1 (B.removeBinders names) p.2 body).eval st' ρ' Ψ) →
      W.agrees st.decls ρ →
      G.agreeOnLinked ρ γg →
      G.wfIn st.decls →
      B.agreeOnLinked ρ γ →
      B.wfIn st.decls →
      GhostFns.wellTyped W st.decls ρ Gf →
      tl.wfIn st.decls →
      Term.eval ρ tl = vals →
      (∀ v st' ρ' t, Ψ t st' ρ' → t.wfIn st'.decls → Term.eval ρ' t = v →
        st'.sl W ρ' ∗ TinyML.ValHasType W v body.ty ∗ R ⊢ Φ v) →
      st.sl W ρ ∗ (TinyML.ValsHaveTypes W vals tys ∗
        (Bindings.typedScope W G B Γ γg γ ∗ R)) ⊢ |==> ∃ v, Φ v
  | [], [], tl, vals, G, B, Γ, γg, γ, st, ρ, Ψ, R, Φ,
      heval, hag, hgagree, hgwf, hagree, hbwf, hGf, _htl_wf, _htl_eval, hpost => by
      simp only [compileProductBindersFrom] at heval
      have hbody_eval : (compileGhostExpr W.Θ W.Δ_spec Gf G B Γ body).eval st ρ Ψ := by
        simpa [Bindings.removeBinders, Bindings.removeAll] using VerifM.eval_ret heval
      cases vals with
      | nil =>
          refine BIBase.Entails.trans ?_ (ihBody G B Γ γg γ (R := R) (Φ := Φ)
            hag hgagree hgwf hagree hbwf hGf hbody_eval hpost)
          iintro ⟨Hsl, Hvals, Hctx⟩
          ihave Hemp := (TinyML.ValsHaveTypes.nil W).1 $$ Hvals
          isplitl [Hsl]
          · iexact Hsl
          · iexact Hctx
      | cons v vs =>
          iintro ⟨_Hsl, Hvals, _Hctx⟩
          ihave Hfalse := (TinyML.ValsHaveTypes.cons_nil W v vs).1 $$ Hvals
          iapply false_elim
          iexact Hfalse
  | [], _ty :: _tys, _tl, _vals, _G, _B, _Γ, _γg, _γ, _st, _ρ, _Ψ, _R, _Φ,
      heval, _, _, _, _, _, _, _, _, _ => by
      simp only [compileProductBindersFrom] at heval
      exact (VerifM.eval_fatal heval).elim
  | _b :: _bs, [], _tl, _vals, _G, _B, _Γ, _γg, _γ, _st, _ρ, _Ψ, _R, _Φ,
      heval, _, _, _, _, _, _, _, _, _ => by
      simp only [compileProductBindersFrom] at heval
      exact (VerifM.eval_fatal heval).elim
  | b :: bs, ty :: tys, tl, vals, G, B, Γ, γg, γ, st, ρ, Ψ, R, Φ,
      heval, hag, hgagree, hgwf, hagree, hbwf, hGf, htl_wf, htl_eval, hpost => by
      cases vals with
      | nil =>
          iintro ⟨_Hsl, Hvals, _Hctx⟩
          ihave Hfalse := (TinyML.ValsHaveTypes.nil_cons W ty tys).1 $$ Hvals
          iapply false_elim
          iexact Hfalse
      | cons v vs =>
          simp only [compileProductBindersFrom] at heval
          obtain ⟨hbty, hcont⟩ := VerifM.eval_expectEq (VerifM.eval_bind heval)
          have hhead_wf : (Term.unop UnOp.vhead tl).wfIn st.decls := ⟨trivial, htl_wf⟩
          have htail_wf : (Term.unop UnOp.vtail tl).wfIn st.decls := ⟨trivial, htl_wf⟩
          have hhead_eval : (Term.unop UnOp.vhead tl).eval ρ = v := by
            simp [Term.eval, UnOp.eval, htl_eval]
          have htail_eval : (Term.unop UnOp.vtail tl).eval ρ = vs := by
            simp [Term.eval, UnOp.eval, htl_eval]
          cases hname : b.name with
          | none =>
              simp [hname] at hcont
              have hrec := compileGhostProductBindersFrom_correct W Gf body ihBody bs tys
                (Term.unop UnOp.vtail tl) vs G B Γ γg γ st ρ Ψ R Φ
                (by simpa [Bindings.removeBinders, Bindings.removeAll, hname] using hcont)
                hag hgagree hgwf hagree hbwf hGf htail_wf htail_eval hpost
              refine BIBase.Entails.trans ?_ hrec
              iintro ⟨Hsl, Hvals, Hctx⟩
              ihave Hpair := (TinyML.ValsHaveTypes.cons W v vs ty tys).1 $$ Hvals
              icases Hpair with ⟨_Hv, Hvs⟩
              isplitl [Hsl]
              · iexact Hsl
              · isplitl [Hvs]
                · iexact Hvs
                · iexact Hctx
          | some x =>
              simp [hname] at hcont
              have hdecl_eval := VerifM.eval_bind hcont
              have hdecl := VerifM.eval_decl hdecl_eval
              set x' := st.freshConst (some x) .value
              set st₁ : TransState := { st with decls := st.decls.addConst x' }
              set ρ₁ := ρ.updateConst .value x'.name v
              have hassume := VerifM.eval_assumePure (VerifM.eval_bind (hdecl v))
              have hfresh : x'.name ∉ st.decls.allNames := by
                simpa [x'] using TransState.freshConst_fresh st (some x) .value
              have hformula_wf :
                  (Formula.eq .value (.const (.uninterpreted x'.name .value))
                    (Term.unop UnOp.vhead tl)).wfIn st₁.decls := by
                have hstwf : st.decls.wf := (VerifM.eval.wf hdecl_eval).namesDisjoint
                simpa [x', st₁] using
                  (Formula.eq_wfIn_addConst_of_fresh (Δ := st.decls) (c := x')
                    hstwf hhead_wf hfresh)
              have hagreeOn_body : Env.agreeOn st.decls ρ ρ₁ :=
                Env.agreeOn_update_fresh_const hfresh
              have hformula_eval :
                  (Formula.eq .value (.const (.uninterpreted x'.name .value))
                    (Term.unop UnOp.vhead tl)).eval ρ₁ := by
                have hval_same : v = (Term.unop UnOp.vhead tl).eval ρ₁ :=
                  hhead_eval.symm.trans (Term.eval_env_agree hhead_wf hagreeOn_body)
                simpa [Formula.eval, Term.eval, Const.denote, ρ₁, Env.updateConst]
                  using hval_same
              have hrec_eval := hassume hformula_wf hformula_eval
              set st₂ : TransState := { st₁ with
                asserts := (Formula.eq .value (.const (.uninterpreted x'.name .value))
                  (Term.unop UnOp.vhead tl)) :: st₁.asserts }
              have hρ_agree : Env.agreeOn (Signature.ofConsts (G.map Prod.snd)) ρ₁ ρ := by
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · intro y hy; cases hy
                · intro y' hy'
                  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy'
                  exact (hagreeOn_body.2.1 p.2 (hgwf p hp)).symm
                · intro z hz; cases hz
                · intro z hz; cases hz
                · intro z hz; cases hz
                · intro z hz; cases hz
                · intro z hz; cases hz
              have hρ_lookup : ρ₁.consts .value x'.name = v := by
                simp [ρ₁, Env.updateConst]
              have hgagree₁ : Bindings.agreeOnLinked ((x, x') :: G) ρ₁
                  (Runtime.Subst.update γg x v) := by
                have h := Bindings.agreeOnLinked_cons (B := G) (x := x) (v := x') (γ := γg)
                  hgagree hρ_agree (hvty := (rfl : x'.sort = .value))
                rwa [hρ_lookup] at h
              have hgwf₁ : Bindings.wfIn ((x, x') :: G) st₂.decls := by
                simpa [st₂, st₁] using Bindings.wfIn_cons hgwf
              have hagree₁ : Bindings.agreeOnLinked (B.remove x) ρ₁ γ :=
                Bindings.agreeOnLinked_remove
                  (Bindings.agreeOnLinked_env_agree hagree hagreeOn_body hbwf) x
              have hbwf₁ : Bindings.wfIn (B.remove x) st₂.decls := fun p hp =>
                (Signature.Subset.subset_addConst st.decls x').consts _
                  (hbwf p (Bindings.mem_of_mem_remove hp))
              have hag₁ := hag.step
                (Signature.Subset.subset_addConst st.decls x') hagreeOn_body
              have hGf₁ := hGf.step
                (Signature.Subset.subset_addConst st.decls x') hagreeOn_body
                (Signature.wf_addConst (VerifM.eval.wf hdecl_eval).namesDisjoint hfresh)
              have hrec := compileGhostProductBindersFrom_correct W Gf body ihBody bs tys
                (Term.unop UnOp.vtail tl) vs ((x, x') :: G) (B.remove x) (Γ.extend x ty)
                (Runtime.Subst.update γg x v) γ st₂ ρ₁ Ψ R Φ
                (by simpa [Bindings.removeBinders, Bindings.removeAll, hname] using hrec_eval)
                hag₁ hgagree₁ hgwf₁ hagree₁ hbwf₁ hGf₁
                (by
                  have htail_wf₁ := Term.wfIn_mono (Term.unop UnOp.vtail tl) htail_wf
                    (Signature.Subset.subset_addConst st.decls x')
                    (Signature.wf_addConst (VerifM.eval.wf hdecl_eval).namesDisjoint hfresh)
                  simpa [st₂, st₁] using htail_wf₁)
                (by
                  rw [Term.eval_env_agree htail_wf (Env.agreeOn_symm hagreeOn_body)]
                  exact htail_eval)
                hpost
              refine BIBase.Entails.trans ?_ hrec
              iintro ⟨Hsl, Hvals, #HT, HR⟩
              ihave Hpair := (TinyML.ValsHaveTypes.cons W v vs ty tys).1 $$ Hvals
              icases Hpair with ⟨Hv, Hvs⟩
              have hinterp_eq : SpatialContext.interp W ρ st.owns ⊢
                  SpatialContext.interp W ρ₁ st.owns :=
                (SpatialContext.interp_env_agree W (VerifM.eval.wf hdecl_eval).ownsWf
                  (Env.agreeOn_update_fresh_const hfresh)).1
              isplitl [Hsl]
              · simp only [TransState.sl_eq]
                iapply hinterp_eq
                iexact Hsl
              · isplitl [Hvs]
                · iexact Hvs
                · isplitl [Hv]
                  · iapply (Bindings.typedScope_cons_ghost (W := W) (G := G) (B := B) (Γ := Γ)
                      (γg := γg) (γ := γ) (x := x) (v := x') (te := ty) (w := v))
                    · iexact HT
                    · iexact Hv
                  · iexact HR

theorem compileGhostLetProd_correct (W : TinyML.World) (Gf : GhostFns)
    (names : List Binder) (e body : Expr)
    (ihE : correctGhostExpr W Gf e) (ihBody : correctGhostExpr W Gf body) :
    correctGhostExpr W Gf (.letProd names e body) := by
  intro G B Γ γg γ st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf heval hpost
  simp only [compileGhostExpr] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  refine bupd_absorb (BIBase.Entails.trans (Helpers.ctx_dup W G B Γ st ρ γg γ R)
    (ihE G B Γ γg γ (R := iprop(Bindings.typedScope W G B Γ γg γ ∗ R))
      (Φ := fun _ => iprop(|==> ∃ v, Φ v))
      hag hgagree hgwf hagree hbwf hGf (VerifM.eval.decls_grow ρ (VerifM.eval_bind heval)) ?_))
  intro v_e st₁ ρ_e se hΨ_e hse_wf heval_se
  obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
  cases hty : e.ty with
  | tuple tys =>
      simp [hty] at hΨ_e
      have hprod_eval := VerifM.eval_bind (VerifM.eval_ret (VerifM.eval_bind hΨ_e))
      have hagree_e := Bindings.agreeOnLinked_env_agree hagree hagreeOn_e hbwf
      have hgagree_e := Bindings.agreeOnLinked_env_agree hgagree hagreeOn_e hgwf
      have hbwf_e : B.wfIn st₁.decls := fun p hp => hdecls_e.consts _ (hbwf p hp)
      have hgwf_e : G.wfIn st₁.decls := fun p hp => hdecls_e.consts _ (hgwf p hp)
      have hag_e := hag.step hdecls_e hagreeOn_e
      have hGf_e := hGf.step hdecls_e hagreeOn_e (VerifM.eval.wf hΨ_e).namesDisjoint
      istart
      iintro ⟨Hsl, Hve, #HT, HR⟩
      ihave Htuple := (TinyML.ValHasType.tuple W v_e tys).1 $$ Hve
      icases Htuple with ⟨%vs, %hveq, Hvals⟩
      subst hveq
      iapply (compileGhostProductBindersFrom_correct W Gf body ihBody names tys
        (Term.unop UnOp.toValList se) vs G B Γ γg γ st₁ ρ_e _ R Φ
        hprod_eval hag_e hgagree_e hgwf_e hagree_e hbwf_e hGf_e ⟨trivial, hse_wf⟩
        (by simp [Term.eval, UnOp.eval, heval_se]) hpost)
      isplitl [Hsl]
      · iexact Hsl
      · isplitl [Hvals]
        · iexact Hvals
        · isplitl []
          · iexact HT
          · iexact HR
  | prim _ | sum _ | arrow _ _ | ref _ | array _ | ownedArray _ | vec _ | owned _ | empty
  | value | tvar _ | named _ _ =>
      simp [hty] at hΨ_e
      exact (VerifM.eval_fatal (VerifM.eval_bind hΨ_e)).elim

theorem compileGhostIfThenElse_correct (W : TinyML.World) (Gf : GhostFns)
    (cond thn els : Expr) (ty : TinyML.Typ)
    (ihCond : correctGhostExpr W Gf cond) (ihThn : correctGhostExpr W Gf thn)
    (ihEls : correctGhostExpr W Gf els) :
    correctGhostExpr W Gf (.ifThenElse cond thn els ty) := by
  intro G B Γ γg γ st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf heval hpost
  simp only [compileGhostExpr] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  refine bupd_absorb (BIBase.Entails.trans (Helpers.ctx_dup W G B Γ st ρ γg γ R)
    (ihCond G B Γ γg γ (R := iprop(Bindings.typedScope W G B Γ γg γ ∗ R))
      (Φ := fun _ => iprop(|==> ∃ v, Φ v))
      hag hgagree hgwf hagree hbwf hGf (VerifM.eval.decls_grow ρ (VerifM.eval_bind heval)) ?_))
  intro v_c st₁ ρ_c sc hΨ_c hsc_wf heval_c
  obtain ⟨hdecls_c, hagreeOn_c, hΨ_c⟩ := hΨ_c
  have hagree_c := Bindings.agreeOnLinked_env_agree hagree hagreeOn_c hbwf
  have hgagree_c := Bindings.agreeOnLinked_env_agree hgagree hagreeOn_c hgwf
  have hbwf_c : B.wfIn st₁.decls := fun p hp => hdecls_c.consts _ (hbwf p hp)
  have hgwf_c : G.wfIn st₁.decls := fun p hp => hdecls_c.consts _ (hgwf p hp)
  have hag_c := hag.step hdecls_c hagreeOn_c
  have hGf_c := hGf.step hdecls_c hagreeOn_c (VerifM.eval.wf hΨ_c).namesDisjoint
  obtain ⟨hcond_bool, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
  obtain ⟨hthn_ty, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
  obtain ⟨hels_ty, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
  have hall := VerifM.eval_all (VerifM.eval_bind hΨ_c)
  have hwf_ne : (Formula.not sc.isFalse).wfIn st₁.decls := by
    simp only [Term.isFalse, Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, _root_.and_true]
    exact hsc_wf
  have hwf_eq : sc.isFalse.wfIn st₁.decls := by
    simp only [Term.isFalse, Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, _root_.and_true]
    exact hsc_wf
  have htrue_cont := VerifM.eval_assumePure (VerifM.eval_bind (hall true (by simp)))
  have hfalse_cont := VerifM.eval_assumePure (VerifM.eval_bind (hall false (by simp)))
  let st_thn : TransState := { st₁ with asserts := sc.isFalse.not :: st₁.asserts }
  let st_els : TransState := { st₁ with asserts := sc.isFalse :: st₁.asserts }
  have hbool_cases :
      st₁.sl W ρ_c ∗ (TinyML.ValHasType W v_c cond.ty ∗ (Bindings.typedScope W G B Γ γg γ ∗ R)) ⊢
        st₁.sl W ρ_c ∗ iprop(⌜v_c = .bool false ∨ v_c = .bool true⌝) ∗
          (Bindings.typedScope W G B Γ γg γ ∗ R) := by
    rw [hcond_bool]
    iintro ⟨Howns, Hv, #HT, HR⟩
    ihave Hv_bool := (TinyML.ValHasType.bool W v_c).1 $$ Hv
    icases Hv_bool with ⟨%b, %hv⟩
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · exact pure_intro (by subst hv; cases b <;> simp)
      · isplitl []
        · iexact HT
        · iexact HR
  refine hbool_cases.trans ?_
  istart
  iintro ⟨Howns, Hbool, #HT, HR⟩
  icases Hbool with %hbool
  rcases hbool with hfalse_val | htrue_val
  · subst hfalse_val
    have heval_els : (compileGhostExpr W.Θ W.Δ_spec Gf G B Γ els).eval st_els ρ_c Ψ :=
      hfalse_cont hwf_eq (by
        simp only [Term.isFalse, Formula.eval, Term.eval, UnOp.eval, Const.denote]
        exact heval_c)
    have hres : st_els.sl W ρ_c ∗ (Bindings.typedScope W G B Γ γg γ ∗ R) ⊢ |==> ∃ v, Φ v :=
      ihEls G B Γ γg γ (R := R) (Φ := Φ) hag_c hgagree_c hgwf_c hagree_c hbwf_c hGf_c
        (VerifM.eval.decls_grow ρ_c heval_els)
        (fun v st' ρ' t hΨ' hs hw => by simpa [hels_ty] using hpost v st' ρ' t hΨ'.2.2 hs hw)
    iapply ((show st₁.sl W ρ_c ∗ (Bindings.typedScope W G B Γ γg γ ∗ R) ⊢
        st_els.sl W ρ_c ∗ (Bindings.typedScope W G B Γ γg γ ∗ R) by
      simp [st_els, TransState.sl]).trans hres)
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · iexact HT
      · iexact HR
  · subst htrue_val
    have heval_thn : (compileGhostExpr W.Θ W.Δ_spec Gf G B Γ thn).eval st_thn ρ_c Ψ :=
      htrue_cont hwf_ne (by
        simp only [Term.isFalse, Formula.eval, Term.eval, UnOp.eval, Const.denote]
        rw [heval_c]
        simp)
    have hres : st_thn.sl W ρ_c ∗ (Bindings.typedScope W G B Γ γg γ ∗ R) ⊢ |==> ∃ v, Φ v :=
      ihThn G B Γ γg γ (R := R) (Φ := Φ) hag_c hgagree_c hgwf_c hagree_c hbwf_c hGf_c
        (VerifM.eval.decls_grow ρ_c heval_thn)
        (fun v st' ρ' t hΨ' hs hw => by simpa [hthn_ty] using hpost v st' ρ' t hΨ'.2.2 hs hw)
    iapply ((show st₁.sl W ρ_c ∗ (Bindings.typedScope W G B Γ γg γ ∗ R) ⊢
        st_thn.sl W ρ_c ∗ (Bindings.typedScope W G B Γ γg γ ∗ R) by
      simp [st_thn, TransState.sl]).trans hres)
    isplitl [Howns]
    · iexact Howns
    · isplitl []
      · iexact HT
      · iexact HR


/-- A ghost call. Ghost code takes no step, so what the callee guarantees is
`Spec.isGhostPrecondFor` and not `Spec.isPrecondFor`: instead of the weakest
precondition of an application, a value of the result type exists at which the
obligation holds. -/
theorem compileGhostApp_correct (W : TinyML.World) (Gf : GhostFns)
    (hwf : W.wf)
    (fn : Expr) (args gargs : List Expr) (aty : TinyML.Typ)
    (ihArgs : correctGhostExprs W Gf args) (ihGArgs : correctGhostExprs W Gf gargs) :
    correctGhostExpr W Gf (.app fn args gargs aty) := by
  intro G B Γ γg γ st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf heval hpost
  simp only [Expr.WithTypeVars.ty] at hpost
  cases fn with
  | var f inst fty =>
    simp only [compileGhostExpr] at heval
    split at heval
    case _ argTys retTy s guard hlookup =>
      cases hcheck : Spec.checkWf s W.Δ_spec with
      | error msg => rw [hcheck] at heval; exact (VerifM.eval_fatal heval).elim
      | ok u =>
      cases u
      rw [hcheck] at heval
      have hswf : s.wfIn W.Δ_spec := Spec.checkWf_ok hcheck
      obtain ⟨hret_eq, heval⟩ := VerifM.eval_bind_expectEq heval
      obtain ⟨hlen_e, heval⟩ := VerifM.eval_bind_expectEq heval
      have heval_args := VerifM.eval_bind heval
      refine bupd_absorb (BIBase.Entails.trans (Helpers.ctx_dup W G B Γ st ρ γg γ R)
        (ihArgs G B Γ γg γ (R := iprop(Bindings.typedScope W G B Γ γg γ ∗ R))
          (Φ := fun _ => iprop(|==> ∃ v, Φ v))
          hag hgagree hgwf hagree hbwf hGf (VerifM.eval.decls_grow ρ heval_args) ?_))
      intro vs st_args ρ_args sargs hΨ_args hsargs_wf heval_sargs
      obtain ⟨hdecls_args, hagreeOn_args, hΨ_args⟩ := hΨ_args
      have hag_args := hag.step hdecls_args hagreeOn_args
      have hGf_args := hGf.step hdecls_args hagreeOn_args
        (VerifM.eval.wf hΨ_args).namesDisjoint
      have hagree_args := Bindings.agreeOnLinked_env_agree hagree hagreeOn_args hbwf
      have hgagree_args := Bindings.agreeOnLinked_env_agree hgagree hagreeOn_args hgwf
      have hbwf_args : B.wfIn st_args.decls := fun p hp => hdecls_args.consts _ (hbwf p hp)
      have hgwf_args : G.wfIn st_args.decls := fun p hp => hdecls_args.consts _ (hgwf p hp)
      have hlen_sargs : sargs.length = vs.length := by
        simpa [Terms.Eval] using List.Forall₂.length_eq heval_sargs
      have heval_gargs := VerifM.eval_bind hΨ_args
      refine bupd_absorb (BIBase.Entails.trans ?_
        (ihGArgs G B Γ γg γ
          (R := iprop(TinyML.ValsHaveTypes W vs (args.map Expr.WithTypeVars.ty) ∗ R))
          (Φ := fun _ => iprop(|==> ∃ v, Φ v))
          hag_args hgagree_args hgwf_args hagree_args hbwf_args hGf_args
          (VerifM.eval.decls_grow ρ_args heval_gargs) ?_))
      · iintro ⟨Howns, #Hvals, #HT, HR⟩
        isplitl [Howns]
        · iexact Howns
        · isplitl []
          · iexact HT
          · isplitl []
            · iexact Hvals
            · iexact HR
      intro gs st_g ρ_g gterms hΨ_g hgterms_wf heval_gterms
      obtain ⟨hdecls_g, hagreeOn_g, hΨ_g⟩ := hΨ_g
      have hguard := GhostFns.Entry.check_correct (VerifM.eval_bind hΨ_g)
      have hΨ_g := hguard.2
      set typedArgs := (args.map Expr.WithTypeVars.ty).zip sargs with htypedArgs_def
      set typedGArgs := (gargs.map Expr.WithTypeVars.ty).zip gterms with htypedGArgs_def
      have hag_g : W.agrees st_g.decls ρ_g := hag_args.step hdecls_g hagreeOn_g
      have hst_g_wf : st_g.decls.wf := (VerifM.eval.wf hΨ_g).namesDisjoint
      have hGf_g := hGf_args.step hdecls_g hagreeOn_g hst_g_wf
      have hsargs_wf_g : ∀ t ∈ sargs, t.wfIn st_g.decls := fun t ht =>
        Term.wfIn_mono t (hsargs_wf t ht) hdecls_g hst_g_wf
      have htypedArgs_wf : ∀ p ∈ typedArgs, p.2.wfIn st_g.decls :=
        fun p hp => hsargs_wf_g _ (List.of_mem_zip hp).2
      have htypedGArgs_wf : ∀ p ∈ typedGArgs, p.2.wfIn st_g.decls :=
        fun p hp => hgterms_wf _ (List.of_mem_zip hp).2
      have hwf_pred : PredTrans.wfIn
          ((W.Δ_spec.declVars (FiniteSubst.base W.Δ_spec).dom).declVars
            (Spec.argVars s.allArgs)) s.pred := by
        simpa [FiniteSubst.base, Signature.declVars] using hswf
      have hbase_wf : (FiniteSubst.base W.Δ_spec).wfIn W.Δ_spec st_g.decls :=
        FiniteSubst.base_wfIn hag_g.subset hwf.wf hst_g_wf hwf.vars
      have hcall_eval : VerifM.eval
          (Spec.call (FiniteSubst.base W.Δ_spec) argTys retTy s typedArgs typedGArgs) st_g ρ_g
          (fun p st' ρ' => VerifM.eval (pure p.2) st' ρ' Ψ) := VerifM.eval_bind hΨ_g
      obtain ⟨hsub_ty, hsub_gty, happly⟩ :=
        Spec.call_correct W argTys retTy s W.Δ_spec (FiniteSubst.base W.Δ_spec)
          typedArgs typedGArgs st_g ρ_g (fun p st' ρ' => VerifM.eval (pure p.2) st' ρ' Ψ) Φ R
          hlen_e hwf_pred hbase_wf htypedArgs_wf htypedGArgs_wf hcall_eval
          (fun v st' ρ' t hΨ' hwft heval' => by
            have h := hpost v st' ρ' t (VerifM.eval_ret hΨ') hwft heval'
            rw [← hret_eq] at h
            iintro ⟨Howns', HR', Hty⟩
            iapply h
            isplitl [Howns']
            · iexact Howns'
            · isplitl [Hty]
              · iexact Hty
              · iexact HR')
      have hagree_ρ_g : Env.agreeOn W.Δ_spec W.ρ_spec ρ_g := hag_g.agree
      istart
      iintro ⟨Howns, #Hgvals, #Hvals, HR⟩
      ihave Hlen := TinyML.ValsHaveTypes.length_eq $$ Hvals
      ipure Hlen
      ihave Hglen := TinyML.ValsHaveTypes.length_eq $$ Hgvals
      ipure Hglen
      have hlen_typed : (args.map Expr.WithTypeVars.ty).length = sargs.length := by
        rw [← Hlen]; exact hlen_sargs.symm
      have hlen_gtyped : (gargs.map Expr.WithTypeVars.ty).length = gterms.length := by
        rw [← Hglen]
        simpa [Terms.Eval] using (List.Forall₂.length_eq heval_gterms).symm
      obtain ⟨hfst, heval_args_map⟩ := typedArgs_split hlen_typed heval_sargs
      obtain ⟨hgfst, heval_gargs_map⟩ := typedArgs_split hlen_gtyped heval_gterms
      have hsub_ty' : args.map Expr.WithTypeVars.ty = argTys := by
        simpa [htypedArgs_def, hfst] using hsub_ty
      have hsub_gty' : gargs.map Expr.WithTypeVars.ty = s.ghost.map Prod.snd := by
        simpa [htypedGArgs_def, hgfst] using hsub_gty
      have hvslen : vs.length = argTys.length := by
        rw [Hlen, hsub_ty']
      have hgslen : gs.length = s.ghost.length := by
        rw [Hglen, hsub_gty', List.length_map]
      -- The argument terms still denote the same values in the state the call is
      -- made in; the ghost arguments were compiled there, so they need no transport.
      have heval_sargs_map : typedArgs.map (fun p => p.2.eval ρ_g) = vs := by
        refine Eq.trans (List.map_congr_left fun p hp => ?_) heval_args_map
        exact Term.eval_env_agree (hsargs_wf _ (List.of_mem_zip hp).2)
          (Env.agreeOn_symm hagreeOn_g)
      have happly' :
          st_g.sl W ρ_g ∗ R ⊢
            PredTrans.apply (TinyML.ValHasType W) (fun r => TinyML.ValHasType W r retTy -∗ Φ r)
              s.pred (Spec.argsEnv ρ_g s.allArgs (vs ++ gs)) := by
        rw [heval_sargs_map, heval_gargs_map] at happly
        exact happly
      -- A finished declaration gives the guarantee outright; the declaration
      -- being checked gives it only below its rank, which is what the call-site
      -- guard has just established.
      have hkey :
          TinyML.ValsRel (TinyML.ValHasType W) vs argTys ∗
              TinyML.ValsRel (TinyML.ValHasType W) gs (s.ghost.map Prod.snd) ∗
              PredTrans.apply (TinyML.ValHasType W)
                (fun r => TinyML.ValHasType W r retTy -∗ Φ r) s.pred
                (Spec.argsEnv ρ_g s.allArgs (vs ++ gs)) ⊢ |==> ∃ v, Φ v := by
        have hentry := hGf_g W.eta f argTys retTy s guard hlookup
        cases guard with
        | none =>
          istart
          iintro ⟨Hvs, Hgs, Hpred⟩
          iapply (Spec.isGhostPrecondFor.apply (W := W) (V := TinyML.ValHasType W) (s := s)
            (argTys := argTys) (retTy := retTy) (ρ := ρ_g) (Φ := Φ) hagree_ρ_g hvslen hgslen)
          isplitl []
          · iapply hentry
          · isplitl [Hvs]
            · iexact Hvs
            · isplitl [Hgs]
              · iexact Hgs
              · iexact Hpred
        | some g =>
          obtain ⟨-, hmwf, hreal⟩ := hentry
          obtain ⟨hlen_g, hcond⟩ := hguard.1 g rfl
          have hterms_eval : Terms.Eval ρ_g (sargs ++ gterms) (vs ++ gs) :=
            List.rel_append
              (Terms.Eval.env_agree hsargs_wf hagreeOn_g heval_sargs) heval_gterms
          have hsubst := Spec.eval_argSubst (Δ := W.Δ_spec) (names := s.allArgs)
            (terms := sargs ++ gterms) (vals := vs ++ gs) hlen_g.symm hterms_eval
            g.measure.term hmwf
          have hlenargs : s.allArgs.length ≤ (vs ++ gs).length := by
            rw [← hlen_g, List.Forall₂.length_eq hterms_eval]
          have hdenote : g.measure.denote s ρ_g vs gs = g.measure.denote s W.ρ_spec vs gs := by
            simp only [Typed.Measure.denote]
            rw [Term.eval_env_agree hmwf
              (Spec.argsEnv_agreeOn (Env.agreeOn_symm hagree_ρ_g) s.allArgs (vs ++ gs) hlenargs)]
          simp only [GhostFns.Guard.condition, Formula.eval, Term.eval, BinPred.eval,
            Const.denote] at hcond
          obtain ⟨-, hnonneg, hlt⟩ := hcond
          have hrank : g.measure.denote s W.ρ_spec vs gs < (Term.eval ρ_g g.rank).toNat := by
            rw [← hdenote]
            simp only [Typed.Measure.denote, ← hsubst]
            exact (Int.toNat_lt_toNat (lt_of_le_of_lt hnonneg hlt)).mpr hlt
          istart
          iintro ⟨Hvs, Hgs, Hpred⟩
          iapply (Spec.isGhostPrecondForAt.apply (W := W) (V := TinyML.ValHasType W) (s := s)
            (argTys := argTys) (retTy := retTy) (ρ := ρ_g) (Φ := Φ) hagree_ρ_g hvslen hgslen hrank)
          isplitl []
          · iapply hreal
          · isplitl [Hvs]
            · iexact Hvs
            · isplitl [Hgs]
              · iexact Hgs
              · iexact Hpred
      iapply hkey
      isplitl []
      · rw [← hsub_ty']
        iexact Hvals
      · isplitl []
        · rw [← hsub_gty']
          iexact Hgvals
        · iapply happly'
          isplitl [Howns]
          · iexact Howns
          · iexact HR
    case _ =>
      exact (VerifM.eval_fatal heval).elim
  | _ =>
    simp only [compileGhostExpr] at heval
    exact (VerifM.eval_fatal heval).elim

theorem compileGhostMatch_correct (W : TinyML.World) (Gf : GhostFns)
    (scrut : Expr) (branches : List (Binder × Expr)) (ty : TinyML.Typ)
    (ihScrut : correctGhostExpr W Gf scrut)
    (ihBranches : correctGhostBranches W Gf branches) :
    correctGhostExpr W Gf (.match_ scrut branches ty) := by
  intro G B Γ γg γ st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf heval hpost
  simp only [compileGhostExpr] at heval
  simp only [Expr.WithTypeVars.ty] at hpost
  refine bupd_absorb (BIBase.Entails.trans (Helpers.ctx_dup W G B Γ st ρ γg γ R)
    (ihScrut G B Γ γg γ (R := iprop(Bindings.typedScope W G B Γ γg γ ∗ R))
      (Φ := fun _ => iprop(|==> ∃ v, Φ v))
      hag hgagree hgwf hagree hbwf hGf (VerifM.eval.decls_grow ρ (VerifM.eval_bind heval)) ?_))
  intro v_scrut st_scrut ρ_scrut se_scrut hΨ_scrut hse_wf heval_se
  obtain ⟨hdecls_scrut, hagreeOn_scrut, hΨ_scrut⟩ := hΨ_scrut
  cases hscrut_ty : sumComponents? W.Θ scrut.ty with
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
              let i ← VerifM.all (List.range
                (compileGhostBranches W.Θ W.Δ_spec Gf G B Γ se_scrut ts branches 0).length)
              match (compileGhostBranches W.Θ W.Δ_spec Gf G B Γ se_scrut ts branches 0)[i]? with
              | some m => m
              | none => VerifM.fatal "match branch index out of range").eval st_scrut ρ_scrut Ψ := by
          simpa [if_pos hlen, if_pos htys] using hΨ_scrut
        have hcb := compileGhostBranches_length_get W.Θ W.Δ_spec Gf G B Γ se_scrut ts branches 0
        have hall := VerifM.eval_all (VerifM.eval_bind hΨ_scrut')
        have hag_scrut := hag.step hdecls_scrut hagreeOn_scrut
        have hGf_scrut := hGf.step hdecls_scrut hagreeOn_scrut
          (VerifM.eval.wf hΨ_scrut).namesDisjoint
        have hagree_scrut := Bindings.agreeOnLinked_env_agree hagree hagreeOn_scrut hbwf
        have hgagree_scrut := Bindings.agreeOnLinked_env_agree hgagree hagreeOn_scrut hgwf
        have hbwf_scrut : B.wfIn st_scrut.decls := fun p hp => hdecls_scrut.consts _ (hbwf p hp)
        have hgwf_scrut : G.wfIn st_scrut.decls := fun p hp => hdecls_scrut.consts _ (hgwf p hp)
        iintro ⟨Hsl, Hscrut, #HT, HR⟩
        ihave Hscrut_sum :=
          ((valHasType_sumComponents hscrut_ty).1.trans
            (TinyML.ValHasType.sum W v_scrut ts).1) $$ Hscrut
        icases Hscrut_sum with ⟨%tag, %v_payload, %hval_eq, Hsum⟩
        ihave %htag_bound := TinyML.ValSumRel.bound $$ Hsum
        have htag_branches : tag < branches.length := hlen ▸ htag_bound
        have htag_range : tag ∈ List.range
            (compileGhostBranches W.Θ W.Δ_spec Gf G B Γ se_scrut ts branches 0).length := by
          rw [hcb.1]
          exact List.mem_range.mpr htag_branches
        have heval_tag := hall tag htag_range
        have hcb_get := hcb.2 tag htag_branches
        simp [hcb_get, show branches[tag]? = some branches[tag] from
          List.getElem?_eq_some_iff.mpr ⟨htag_branches, rfl⟩] at heval_tag
        have hget : ts[tag]? = some (ts[tag]?.getD .value) := by
          rw [List.getElem?_eq_getElem htag_bound]
          simp
        have hbranch := ihBranches G B Γ γg γ se_scrut ts.length ts 0 (R := R) (Φ := Φ)
          hag_scrut hgagree_scrut hgwf_scrut hagree_scrut hbwf_scrut hGf_scrut hse_wf
          (fun j hj v st' ρ' t hΨ' hs hw => by
            iintro ⟨Hsl', Hv, HR'⟩
            iapply (hpost v st' ρ' t hΨ' hs hw)
            isplitl [Hsl']
            · iexact Hsl'
            · isplitl [Hv]
              · rw [← htys (branches[j]) (List.getElem_mem _)]
                iexact Hv
              · iexact HR')
          tag htag_branches (by simpa [Nat.zero_add] using heval_tag)
          v_payload ((Nat.zero_add tag).symm ▸ (heval_se.trans hval_eq))
        simp only [Nat.zero_add] at hbranch
        iapply hbranch
        isplitl [Hsl]
        · iexact Hsl
        · isplitl [Hsum]
          · iapply (TinyML.ValSumRel.of_getElem? (W := W) hget)
            iexact Hsum
          · isplitl []
            · iexact HT
            · iexact HR
      · have hΨ_bad :
            (VerifM.fatal "match branch type annotation mismatch").eval st_scrut ρ_scrut Ψ := by
          simpa [if_pos hlen, if_neg htys] using hΨ_scrut
        exact (VerifM.eval_fatal hΨ_bad).elim

theorem compileGhostSingleBranch_correct (W : TinyML.World) (Gf : GhostFns)
    (binder : Binder) (body : Expr) (ihBody : correctGhostExpr W Gf body) :
    correctGhostBranch W Gf (binder, body) := by
  intro G B Γ γg γ sc n i ty_i st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf hsc_wf heval hpost
    payload hsc_eval
  simp only [compileGhostBranch] at heval
  obtain ⟨_hbty, hcont⟩ := VerifM.eval_expectEq (VerifM.eval_bind heval)
  have heval_decl := VerifM.eval_bind hcont
  have hdecl := VerifM.eval_decl heval_decl
  set xv := TransState.freshConst binder.name .value st with hxv_def
  set st₁ : TransState := { decls := st.decls.addConst xv, asserts := st.asserts, owns := st.owns }
  set ρ₁ := ρ.updateConst .value xv.name payload
  have hxv_fresh : xv.name ∉ st.decls.allNames := TransState.freshConst_fresh st binder.name .value
  have hstwf : st.decls.wf := (VerifM.eval.wf heval_decl).namesDisjoint
  have hxv_wf : (Term.const (.uninterpreted xv.name .value)).wfIn st₁.decls := by
    simpa [st₁] using
      (Term.const_wfIn_addConst_of_fresh (Δ := st.decls) (c := xv) hstwf hxv_fresh)
  have hformula_wf : (Formula.eq .value sc
      (.unop (.ofInj i n) (.const (.uninterpreted xv.name .value)))).wfIn st₁.decls :=
    ⟨Term.wfIn_mono sc hsc_wf (Signature.Subset.subset_addConst _ _)
      (Signature.wf_addConst hstwf hxv_fresh), trivial, hxv_wf⟩
  have hagreeOn_st : Env.agreeOn st.decls ρ ρ₁ := Env.agreeOn_update_fresh_const hxv_fresh
  have hformula_eval : Formula.eval ρ₁
      (Formula.eq .value sc (.unop (.ofInj i n) (.const (.uninterpreted xv.name .value)))) := by
    simp [Formula.eval, Term.eval, UnOp.eval]
    rw [Term.eval_env_agree hsc_wf (Env.agreeOn_symm hagreeOn_st), hsc_eval]
    simp [ρ₁, Env.updateConst]
  have heval_assumeAll :=
    VerifM.eval_assumePure (VerifM.eval_bind (hdecl payload)) hformula_wf hformula_eval
  have hxv_eval : (Term.const (.uninterpreted xv.name .value)).eval ρ₁ = payload := by
    simp [Term.eval, Const.denote, ρ₁, Env.updateConst]
  have hinterp_eq : SpatialContext.interp W ρ st.owns ⊢ SpatialContext.interp W ρ₁ st.owns :=
    (SpatialContext.interp_env_agree W (VerifM.eval.wf heval_decl).ownsWf
      (Env.agreeOn_update_fresh_const hxv_fresh)).1
  istart
  iintro ⟨Howns, Hpay, #HT, HR⟩
  iintuitionistic Hpay
  ihave Hcheck := TinyML.typeConstraints_hold (ty := ty_i)
      (t := Term.const (.uninterpreted xv.name .value))
      (ρ := ρ₁) (W := W) (v := payload) hxv_eval $$ Hpay
  ipure Hcheck
  obtain ⟨st₂, hst₂_decls, hst₂_owns, _, heval_body'⟩ :=
    VerifM.eval_assumeAll (VerifM.eval_bind heval_assumeAll)
      (fun φ hφ => TinyML.typeConstraints_wfIn hxv_wf φ hφ) (fun φ hφ => Hcheck φ hφ)
  have hsl_trans : st.sl W ρ ⊢ st₂.sl W ρ₁ := by
    simp only [TransState.sl_eq, hst₂_owns]
    exact hinterp_eq
  cases hname : binder.name with
  | none =>
    simp [hname] at heval_body'
    have hagree₁ : B.agreeOnLinked ρ₁ γ :=
      Bindings.agreeOnLinked_env_agree hagree hagreeOn_st hbwf
    have hgagree₁ : G.agreeOnLinked ρ₁ γg :=
      Bindings.agreeOnLinked_env_agree hgagree hagreeOn_st hgwf
    have hbwf₁ : B.wfIn st₂.decls := hst₂_decls ▸ fun p hp => List.Mem.tail _ (hbwf p hp)
    have hgwf₁ : G.wfIn st₂.decls := hst₂_decls ▸ fun p hp => List.Mem.tail _ (hgwf p hp)
    have hag₁ := hag.step (Signature.Subset.subset_addConst st.decls xv) hagreeOn_st
    have hGf₁ := hGf.step (Signature.Subset.subset_addConst st.decls xv) hagreeOn_st
      (Signature.wf_addConst hstwf hxv_fresh)
    have heval_body'' :
        (compileGhostExpr W.Θ W.Δ_spec Gf G B (Γ.extendBinder binder ty_i) body).eval st₂ ρ₁ Ψ := by
      simpa [ρ₁, xv, hname] using heval_body'
    iapply (ihBody G B (Γ.extendBinder binder ty_i) γg γ (R := R) (Φ := Φ)
      (hst₂_decls ▸ hag₁) hgagree₁ hgwf₁ hagree₁ hbwf₁ (hst₂_decls ▸ hGf₁)
      (VerifM.eval.decls_grow ρ₁ heval_body'')
      (fun v st' ρ' t hΨ' hs hw => hpost v st' ρ' t hΨ'.2.2 hs hw))
    isplitl [Howns]
    · iapply hsl_trans
      iexact Howns
    · isplitl []
      · simp only [TinyML.TyCtx.extendBinder, hname]
        iexact HT
      · iexact HR
  | some x =>
    simp [hname, TinyML.TyCtx.extendBinder] at heval_body'
    have hρ_agree : Env.agreeOn (Signature.ofConsts (G.map Prod.snd)) ρ₁ ρ := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro w hw; cases hw
      · intro c hc
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
        exact (hagreeOn_st.2.1 p.2 (hgwf p hp)).symm
      · intro z hz; cases hz
      · intro z hz; cases hz
      · intro z hz; cases hz
      · intro z hz; cases hz
      · intro z hz; cases hz
    have hρ₁_lookup : ρ₁.consts .value xv.name = payload := by simp [ρ₁, Env.updateConst]
    have hgagree₁ : Bindings.agreeOnLinked ((x, xv) :: G) ρ₁
        (Runtime.Subst.update γg x payload) := by
      have h := Bindings.agreeOnLinked_cons (B := G) (x := x) (v := xv) (γ := γg)
        hgagree hρ_agree (hvty := rfl)
      rwa [hρ₁_lookup] at h
    have hgwf₂ : Bindings.wfIn ((x, xv) :: G) st₂.decls := hst₂_decls ▸ Bindings.wfIn_cons hgwf
    have hagree₁ : Bindings.agreeOnLinked (B.remove x) ρ₁ γ :=
      Bindings.agreeOnLinked_remove
        (Bindings.agreeOnLinked_env_agree hagree hagreeOn_st hbwf) x
    have hbwf₂ : Bindings.wfIn (B.remove x) st₂.decls := hst₂_decls ▸ fun p hp =>
      List.Mem.tail _ (hbwf p (Bindings.mem_of_mem_remove hp))
    have hag₁ := hag.step (Signature.Subset.subset_addConst st.decls xv) hagreeOn_st
    have hGf₁ := hGf.step (Signature.Subset.subset_addConst st.decls xv) hagreeOn_st
      (Signature.wf_addConst hstwf hxv_fresh)
    have heval_body'' :
        (compileGhostExpr W.Θ W.Δ_spec Gf ((x, xv) :: G) (B.remove x)
          (Γ.extendBinder binder ty_i) body).eval st₂ ρ₁ Ψ := by
      simpa [ρ₁, xv, TinyML.TyCtx.extendBinder, hname] using heval_body'
    iapply (ihBody ((x, xv) :: G) (B.remove x) (Γ.extendBinder binder ty_i)
      (Runtime.Subst.update γg x payload) γ (R := R) (Φ := Φ)
      (hst₂_decls ▸ hag₁) hgagree₁ hgwf₂ hagree₁ hbwf₂ (hst₂_decls ▸ hGf₁)
      (VerifM.eval.decls_grow ρ₁ heval_body'')
      (fun v st' ρ' t hΨ' hs hw => hpost v st' ρ' t hΨ'.2.2 hs hw))
    isplitl [Howns]
    · iapply hsl_trans
      iexact Howns
    · isplitl [Hpay]
      · simp only [TinyML.TyCtx.extendBinder, hname]
        iapply (Bindings.typedScope_cons_ghost (W := W) (G := G) (B := B) (Γ := Γ)
          (γg := γg) (γ := γ) (x := x) (v := xv) (te := ty_i) (w := payload))
        · iexact HT
        · iexact Hpay
      · iexact HR

theorem compileGhostBranchesNil_correct (W : TinyML.World) (Gf : GhostFns) :
    correctGhostBranches W Gf [] := by
  intro G B Γ γg γ sc n ts idx st ρ Ψ R Φ _ _ _ _ _ _ _ _ j hj
  exact absurd hj (Nat.not_lt_zero _)

theorem compileGhostBranchesCons_correct (W : TinyML.World) (Gf : GhostFns)
    (b : Binder × Expr) (bs : List (Binder × Expr))
    (ihHead : correctGhostBranch W Gf b) (ihTail : correctGhostBranches W Gf bs) :
    correctGhostBranches W Gf (b :: bs) := by
  intro G B Γ γg γ sc n ts idx st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf hsc_wf hpost j hj
  cases j with
  | zero =>
    simp only [Nat.add_zero, List.getElem_cons_zero]
    intro heval
    exact ihHead G B Γ γg γ sc n idx (ts[idx]?.getD .value) hag hgagree hgwf hagree hbwf hGf
      hsc_wf heval (by simpa using hpost 0 hj)
  | succ k =>
    have hk : k < bs.length := by simp at hj; omega
    have hidx : idx + (k + 1) = idx + 1 + k := by omega
    simp only [hidx, List.getElem_cons_succ]
    exact ihTail G B Γ γg γ sc n ts (idx + 1) hag hgagree hgwf hagree hbwf hGf hsc_wf
      (by
        intro j hj' v st' ρ' t hΨ hs hw
        simpa [Nat.add_assoc] using hpost (j + 1) (by simpa using hj') v st' ρ' t hΨ hs hw)
      k hk

theorem compileGhostExprsNil_correct (W : TinyML.World) (Gf : GhostFns) :
    correctGhostExprs W Gf [] := by
  intro G B Γ γg γ st ρ Ψ R Φ _hag _hgagree _hgwf _hagree _hbwf _hGf heval hpost
  simp only [compileGhostExprs] at heval
  obtain heval := VerifM.eval_ret heval
  refine BIBase.Entails.trans ?_ bupd_intro
  iintro ⟨Hsl, #HT, HR⟩
  iexists ([] : List Runtime.Val)
  iapply (hpost [] st ρ [] heval (by simp) .nil)
  isplitl [Hsl]
  · iexact Hsl
  · isplitl []
    · iapply (show iprop(emp) ⊢ TinyML.ValsHaveTypes W [] ([].map Expr.WithTypeVars.ty) by
        simpa [List.map] using (TinyML.ValsHaveTypes.nil W).2)
      iempintro
    · iexact HR

theorem compileGhostExprsCons_correct (W : TinyML.World) (Gf : GhostFns)
    (e : Expr) (rest : List Expr)
    (ihE : correctGhostExpr W Gf e) (ihRest : correctGhostExprs W Gf rest) :
    correctGhostExprs W Gf (e :: rest) := by
  intro G B Γ γg γ st ρ Ψ R Φ hag hgagree hgwf hagree hbwf hGf heval hpost
  simp only [compileGhostExprs] at heval
  have heval_rest := VerifM.eval_bind heval
  refine bupd_absorb (BIBase.Entails.trans (Helpers.ctx_dup W G B Γ st ρ γg γ R)
    (ihRest G B Γ γg γ (R := iprop(Bindings.typedScope W G B Γ γg γ ∗ R))
      (Φ := fun _ => iprop(|==> ∃ vs, Φ vs))
      hag hgagree hgwf hagree hbwf hGf (VerifM.eval.decls_grow ρ heval_rest) ?_))
  intro vs st_rest ρ_rest ts_rest hΨ_rest hwf_rest heval_ts_rest
  obtain ⟨hdecls_rest, hagreeOn_rest, hΨ_rest⟩ := hΨ_rest
  have hag_rest := hag.step hdecls_rest hagreeOn_rest
  have hGf_rest := hGf.step hdecls_rest hagreeOn_rest
    (VerifM.eval.wf hΨ_rest).namesDisjoint
  have hgagree_rest := Bindings.agreeOnLinked_env_agree hgagree hagreeOn_rest hgwf
  have hagree_rest := Bindings.agreeOnLinked_env_agree hagree hagreeOn_rest hbwf
  have hgwf_rest : G.wfIn st_rest.decls := fun p hp => hdecls_rest.consts _ (hgwf p hp)
  have hbwf_rest : B.wfIn st_rest.decls := fun p hp => hdecls_rest.consts _ (hbwf p hp)
  have heval_e := VerifM.eval_bind hΨ_rest
  refine bupd_forget (BIBase.Entails.trans ?_
    (ihE G B Γ γg γ
      (R := iprop(TinyML.ValsHaveTypes W vs (rest.map Expr.WithTypeVars.ty) ∗ R))
      (Φ := fun _ => iprop(∃ vs, Φ vs))
      hag_rest hgagree_rest hgwf_rest hagree_rest hbwf_rest hGf_rest
      (VerifM.eval.decls_grow ρ_rest heval_e) ?_))
  · iintro ⟨Hsl, Hvs, #HT, HR⟩
    isplitl [Hsl]
    · iexact Hsl
    · isplitl []
      · iexact HT
      · isplitl [Hvs]
        · iexact Hvs
        · iexact HR
  intro v st' ρ' t hΨ_e ht_wf ht_eval
  obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
  have hwfst' : st'.decls.wf := (VerifM.eval.wf hΨ_e).namesDisjoint
  obtain hΨ_e := VerifM.eval_ret hΨ_e
  have hwf_cons : ∀ u ∈ t :: ts_rest, u.wfIn st'.decls := by
    intro u hu
    simp only [List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ht_wf
    · exact Term.wfIn_mono _ (hwf_rest u hu) hdecls_e hwfst'
  have heval_cons : Terms.Eval ρ' (t :: ts_rest) (v :: vs) :=
    Terms.Eval.cons ht_eval
      (Terms.Eval.env_agree (fun u hu => hwf_rest u hu) hagreeOn_e heval_ts_rest)
  iintro ⟨Hsl, Hv, Hvs, HR⟩
  iexists (v :: vs)
  iapply (hpost (v :: vs) st' ρ' (t :: ts_rest) hΨ_e hwf_cons heval_cons)
  isplitl [Hsl]
  · iexact Hsl
  · isplitl [Hv Hvs]
    · iapply (show TinyML.ValHasType W v e.ty ∗
          TinyML.ValsHaveTypes W vs (rest.map Expr.WithTypeVars.ty) ⊢
          TinyML.ValsHaveTypes W (v :: vs) ((e :: rest).map Expr.WithTypeVars.ty) by
        simpa [List.map] using
          (TinyML.ValsHaveTypes.cons W v vs e.ty (rest.map Expr.WithTypeVars.ty)).2)
      isplitl [Hv]
      · iexact Hv
      · iexact Hvs
    · iexact HR


/-! #### Correctness Theorem -/

mutual
theorem compileGhostExpr_correct (W : TinyML.World)
    (Gf : GhostFns) (hwf : W.wf)
    (e : Expr) : correctGhostExpr W Gf e := by
  cases e with
  | const c => exact compileGhostConst_correct W Gf c
  | var x inst vty => exact compileGhostVar_correct W Gf x inst vty
  | prim n inst ty =>
    exact compileGhostRejected_correct W Gf _ (fun _ _ _ _ _ => ⟨_, rfl⟩)
  | fix self args retTy spec body =>
    exact compileGhostRejected_correct W Gf _ (fun _ _ _ _ _ => ⟨_, rfl⟩)
  | ref ownership e =>
    exact compileGhostRejected_correct W Gf _ (fun _ _ _ _ _ => ⟨_, rfl⟩)
  | deref e ty =>
    exact compileGhostRejected_correct W Gf _ (fun _ _ _ _ _ => ⟨_, rfl⟩)
  | store loc val =>
    exact compileGhostRejected_correct W Gf _ (fun _ _ _ _ _ => ⟨_, rfl⟩)
  | arrayMake ownership len init =>
    exact compileGhostRejected_correct W Gf _ (fun _ _ _ _ _ => ⟨_, rfl⟩)
  | arrayGet arr idx ty =>
    exact compileGhostRejected_correct W Gf _ (fun _ _ _ _ _ => ⟨_, rfl⟩)
  | arraySet arr idx val =>
    exact compileGhostRejected_correct W Gf _ (fun _ _ _ _ _ => ⟨_, rfl⟩)
  | inj tag arity payload ty =>
    exact compileGhostInj_correct W Gf tag arity payload ty
      (compileGhostExpr_correct W Gf hwf payload)
  | assert e =>
    exact compileGhostAssert_correct W Gf e (compileGhostExpr_correct W Gf hwf e)
  | arrayLen arr =>
    exact compileGhostArrayLen_correct W Gf arr (compileGhostExpr_correct W Gf hwf arr)
  | unop op e uty =>
    exact compileGhostUnop_correct W Gf op e uty (compileGhostExpr_correct W Gf hwf e)
  | binop op l r bty =>
    exact compileGhostBinop_correct W Gf op l r bty
      (compileGhostExpr_correct W Gf hwf r) (compileGhostExpr_correct W Gf hwf l)
  | letIn mode b e body =>
    exact compileGhostLetIn_correct W Gf mode b e body
      (compileGhostExpr_correct W Gf hwf e) (compileGhostExpr_correct W Gf hwf body)
  | letProd names e body =>
    exact compileGhostLetProd_correct W Gf names e body
      (compileGhostExpr_correct W Gf hwf e) (compileGhostExpr_correct W Gf hwf body)
  | ifThenElse cond thn els ty =>
    exact compileGhostIfThenElse_correct W Gf cond thn els ty
      (compileGhostExpr_correct W Gf hwf cond) (compileGhostExpr_correct W Gf hwf thn)
      (compileGhostExpr_correct W Gf hwf els)
  | app fn args gargs aty =>
    exact compileGhostApp_correct W Gf hwf fn args gargs aty
      (compileGhostExprs_correct W Gf hwf args)
      (compileGhostExprs_correct W Gf hwf gargs)
  | tuple es =>
    exact compileGhostTuple_correct W Gf es (compileGhostExprs_correct W Gf hwf es)
  | match_ scrut branches ty =>
    exact compileGhostMatch_correct W Gf scrut branches ty
      (compileGhostExpr_correct W Gf hwf scrut)
      (compileGhostBranches_correct W Gf hwf branches)

theorem compileGhostBranch_correct (W : TinyML.World)
    (Gf : GhostFns) (hwf : W.wf)
    (branch : Binder × Expr) : correctGhostBranch W Gf branch := by
  obtain ⟨binder, body⟩ := branch
  exact compileGhostSingleBranch_correct W Gf binder body
    (compileGhostExpr_correct W Gf hwf body)

theorem compileGhostBranches_correct (W : TinyML.World)
    (Gf : GhostFns) (hwf : W.wf)
    (branches : List (Binder × Expr)) : correctGhostBranches W Gf branches := by
  match branches with
  | [] => exact compileGhostBranchesNil_correct W Gf
  | b :: bs =>
    exact compileGhostBranchesCons_correct W Gf b bs
      (compileGhostBranch_correct W Gf hwf b)
      (compileGhostBranches_correct W Gf hwf bs)

theorem compileGhostExprs_correct (W : TinyML.World)
    (Gf : GhostFns) (hwf : W.wf)
    (es : List Expr) : correctGhostExprs W Gf es := by
  match es with
  | [] => exact compileGhostExprsNil_correct W Gf
  | e :: rest =>
    exact compileGhostExprsCons_correct W Gf e rest
      (compileGhostExpr_correct W Gf hwf e)
      (compileGhostExprs_correct W Gf hwf rest)
end

/-! ## Ghost Declarations

A `[@@ghost]` declaration is a lemma. Its body sees only its own parameters, the
specification functions, and the ghost functions already declared: a name the
program binds is not in scope there. A recursive occurrence resolves under a
rank, and a recursive call must lower it.
-/

section Declarations

/-- A ghost parameter binds over the arguments, so it takes the name from them. -/
private def ghostBodyArgs (argNames : List String) (argVars : List FOL.Const)
    (ghostNames : List String) : Bindings :=
  Bindings.removeAll (argNames.zip argVars).reverse ghostNames

private def ghostBodyGhosts (ghostNames : List String) (ghostVars : List FOL.Const) : Bindings :=
  (ghostNames.zip ghostVars).reverse

private def ghostBodyTyCtx (argNames : List String) (argTys : List TinyML.Typ)
    (ghost : List (String × TinyML.Typ)) : TinyML.TyCtx :=
  ghost.foldl (fun ctx p => ctx.extend p.1 p.2)
    ((argNames.zip argTys).foldl (fun ctx p => ctx.extend p.1 p.2) TinyML.TyCtx.empty)

/-- The rank is a constant assumed equal to the measure at the declaration's own
    arguments. The measure must be well-formed in the parameter scope, so that a
    call can read it at its own arguments instead. -/
private def GhostFns.Guard.declare (Δ_spec : Signature) (measure : Typed.Measure)
    (names : List String) (terms : List (Term .value)) : VerifM GhostFns.Guard := do
  match measure.term.checkWf (Δ_spec.declVars (Spec.argVars names)) with
  | .error msg => VerifM.fatal msg
  | .ok () => do
    let m := measure.term.subst (Spec.argSubst Subst.id names terms)
    let Δ ← VerifM.decls
    match m.checkWf Δ with
    | .error msg => VerifM.fatal msg
    | .ok () => do
      let rv ← VerifM.decl (some "rank") .int
      let r : Term .int := .const (.uninterpreted rv.name .int)
      VerifM.assume (.pure (.eq .int r m))
      pure ⟨measure, r⟩

/-- A recursive declaration is callable from its own body, under the rank its
    measure gives its own arguments. -/
private def ValDecl.ghostSelf (Δ_spec : Signature) (Gf : GhostFns) (self : Binder)
    (decreases : Option Typed.Measure) (ty : TinyML.Typ) (s : Spec TinyML.Typ)
    (argVars ghostVars : List FOL.Const) : VerifM GhostFns :=
  match self.name, decreases with
  | none, _ => pure Gf
  | some g, none =>
    VerifM.fatal s!"a recursive ghost declaration needs a [@@decreases] measure: {g}"
  | some g, some measure => do
    let terms := (argVars ++ ghostVars).map fun c => Term.const (.uninterpreted c.name .value)
    let guard ← GhostFns.Guard.declare Δ_spec measure s.allArgs terms
    pure ((g, ⟨ty, some guard⟩) :: Gf)

/-- A recursive declaration with no `[@@decreases]` measure is rejected: there is
    no rank to lower, so its self entry would be inconsistent. The entry keeps
    the arrow the declaration was checked at, so a call at a non-trivial
    instantiation of a polymorphic declaration fails the call's type check. -/
def ValDecl.checkGhost (Θ : TinyML.TypeEnv) (Δ_spec : Signature)
    (Gf : GhostFns) (d : Typed.ValDecl) : VerifM (TinyML.Var × GhostFns.Entry) := do
  let f ← VerifM.expectSome "a ghost declaration must be named" d.name.name
  match d.body with
  | .fix self args retTy (some s) body =>
    match extractArgNames args s.args with
    | .error msg => VerifM.fatal msg
    | .ok argNames =>
    match Spec.checkWf s Δ_spec with
    | .error msg => VerifM.fatal msg
    | .ok () => do
      let argTys := args.map Binder.WithTypeVars.ty
      let ty : TinyML.Typ := .arrow argTys retTy (some s)
      VerifM.seq
        (do
          VerifM.persist
          Spec.implement Δ_spec argTys s fun argVars ghostVars => do
            let Gf' ← ValDecl.ghostSelf Δ_spec Gf self d.decreases ty s argVars ghostVars
            let se ← compileGhostExpr Θ Δ_spec Gf'
              (ghostBodyGhosts (s.ghost.map Prod.fst) ghostVars)
              (ghostBodyArgs argNames argVars (s.ghost.map Prod.fst))
              (ghostBodyTyCtx argNames argTys s.ghost) body
            checkRet retTy body.ty
            pure se)
        (pure (f, ⟨ty, none⟩))
  | _ => VerifM.fatal "a ghost declaration must be a specified function"

/-- The body's scope holds its parameters and nothing else, so its typing
    invariant comes entirely from the arguments the specification relates. -/
private theorem ValDecl.checkGhostBody_correct (W : TinyML.World) (Gf : GhostFns) (hwf : W.wf)
    (s : Spec TinyML.Typ) (argTys : List TinyML.Typ) (retTy : TinyML.Typ) (body : Expr)
    (argNames : List String) (vs gs : List Runtime.Val) (Φ : Runtime.Val → iProp)
    {argVars ghostVars : List FOL.Const} {st' : TransState} {ρ' : Env} {Q : iProp}
    (hag : W.agrees st'.decls ρ')
    (hGf : GhostFns.wellTyped W st'.decls ρ' Gf)
    (hlen_args : argNames.length = argTys.length)
    (hargVars_mem : ∀ v ∈ argVars, v ∈ st'.decls.consts)
    (hargVars_sort : ∀ v ∈ argVars, v.sort = .value)
    (hargVars_lookup : List.Forall₂ (fun av val => ρ'.consts .value av.name = val) argVars vs)
    (hghostVars_mem : ∀ v ∈ ghostVars, v ∈ st'.decls.consts)
    (hghostVars_sort : ∀ v ∈ ghostVars, v.sort = .value)
    (hghostVars_lookup : List.Forall₂ (fun gv val => ρ'.consts .value gv.name = val) ghostVars gs)
    (hbody_eval : VerifM.eval
        (do
          let se ← compileGhostExpr W.Θ W.Δ_spec Gf
            (ghostBodyGhosts (s.ghost.map Prod.fst) ghostVars)
            (ghostBodyArgs argNames argVars (s.ghost.map Prod.fst))
            (ghostBodyTyCtx argNames argTys s.ghost) body
          checkRet retTy body.ty
          pure se)
        st' ρ'
        (fun result st'' ρ'' => ∀ X, result.wfIn st''.decls →
          st''.sl W ρ'' ∗ Q ∗
            ((TinyML.ValHasType W (result.eval ρ'') retTy -∗ Φ (result.eval ρ'')) -∗ X) ⊢ X)) :
    st'.sl W ρ' ∗ TinyML.ValsHaveTypes W vs argTys ∗
      TinyML.ValsHaveTypes W gs (s.ghost.map Prod.snd) ∗ Q ⊢ |==> ∃ v, Φ v := by
  set ghostNames := s.ghost.map Prod.fst with hghostNames_def
  set ghostTys := s.ghost.map Prod.snd with hghostTys_def
  set γ_body := Runtime.Subst.id.updateAllBinder (argNames.map Runtime.Binder.named) vs
    with hγ_body_def
  set γg_body := Runtime.Subst.id.updateAllBinder (ghostNames.map Runtime.Binder.named) gs
    with hγg_body_def
  set Bbody := ghostBodyArgs argNames argVars ghostNames with hBbody_def
  set Gbody := ghostBodyGhosts ghostNames ghostVars with hGbody_def
  set Γ' := ghostBodyTyCtx argNames argTys s.ghost with hΓ'_def
  have hcompile := VerifM.eval_bind hbody_eval
  iintro ⟨Howns, #Hvals, #Hgvals, HQ⟩
  ihave %hlen_vals := TinyML.ValsHaveTypes.length_eq $$ Hvals
  ihave %hlen_gvals := TinyML.ValsHaveTypes.length_eq $$ Hgvals
  have hlen_nv : argNames.length = argVars.length := by
    have := hargVars_lookup.length_eq
    omega
  have hlen_nvl : argNames.length = vs.length := by omega
  have hlen_gv : ghostNames.length = ghostVars.length := by
    have := hghostVars_lookup.length_eq
    simp [hghostNames_def, hghostTys_def] at hlen_gvals ⊢
    omega
  have hlen_gvl : ghostNames.length = gs.length := by
    simp [hghostNames_def, hghostTys_def] at hlen_gvals ⊢; omega
  have hagree_body : Bindings.agreeOnLinked Bbody ρ' γ_body := by
    rw [hBbody_def, hγ_body_def, ghostBodyArgs]
    refine Bindings.agreeOnLinked_removeAll ?_ ghostNames
    simpa using Bindings.agreeOnLinked_updateAllBinder Bindings.empty argNames argVars vs
      Runtime.Subst.id ρ' (Bindings.agreeOnLinked_empty ρ' _) hlen_nv hlen_nvl
      hargVars_sort hargVars_lookup
  have hgagree_body : Bindings.agreeOnLinked Gbody ρ' γg_body := by
    rw [hGbody_def, hγg_body_def, ghostBodyGhosts]
    simpa using Bindings.agreeOnLinked_updateAllBinder Bindings.empty ghostNames ghostVars gs
      Runtime.Subst.id ρ' (Bindings.agreeOnLinked_empty ρ' _) hlen_gv hlen_gvl
      hghostVars_sort hghostVars_lookup
  have hbwf_body : Bindings.wfIn Bbody st'.decls := by
    intro p hp
    rw [hBbody_def, ghostBodyArgs] at hp
    exact hargVars_mem p.2 (List.of_mem_zip (List.mem_reverse.mp
      (Bindings.mem_of_mem_removeAll hp))).2
  have hgwf_body : Bindings.wfIn Gbody st'.decls := by
    intro p hp
    rw [hGbody_def, ghostBodyGhosts] at hp
    exact hghostVars_mem p.2 (List.of_mem_zip (List.mem_reverse.mp hp)).2
  have hts_g : TinyML.ValsHaveTypes W gs ghostTys ⊢ Bindings.typedSubst W Gbody Γ' γg_body := by
    iintro #HvalsG
    iapply (Bindings.typedSubst_of_agreeOnLinked (W := W) hgagree_body)
    unfold Bindings.typedEnv
    imodintro
    iintro %x %x' %sx %σ %hmem %hΓ
    rw [hGbody_def, ghostBodyGhosts] at hmem
    rw [hΓ'_def, ghostBodyTyCtx] at hΓ
    iapply (valHasType_lookup_zip_reverse s.ghost ghostVars gs ρ'
      ((argNames.zip argTys).foldl
        (fun ctx (p : String × TinyML.Typ) => ctx.extend p.1 p.2) TinyML.TyCtx.empty)
      x x' sx σ
      (by rw [← hghostNames_def]; exact hlen_gv)
      (by rw [← hghostNames_def]; exact hlen_gvl)
      (by rw [← hghostNames_def]; exact hmem)
      hΓ hghostVars_lookup)
    rw [← hghostTys_def]
    iassumption
  have hts : TinyML.ValsHaveTypes W vs argTys ⊢ Bindings.typedSubst W Bbody Γ' γ_body := by
    iintro #HvalsArg
    iapply (Bindings.typedSubst_of_agreeOnLinked (W := W) hagree_body)
    unfold Bindings.typedEnv
    imodintro
    iintro %x %x' %sx %σ %hmem %hΓ
    rw [hBbody_def, ghostBodyArgs] at hmem
    obtain ⟨hmem, hx_notin_ghost⟩ := Bindings.lookup_removeAll_eq_some.mp hmem
    rw [hΓ'_def, ghostBodyTyCtx, TinyML.TyCtx.foldl_extend_of_not_mem _ _ x
      (by rw [hghostNames_def] at hx_notin_ghost; exact hx_notin_ghost)] at hΓ
    set args' := argNames.zip argTys with hargs'_def
    have hfst : args'.map Prod.fst = argNames := List.map_fst_zip (by omega)
    have hsnd : args'.map Prod.snd = argTys := List.map_snd_zip (by omega)
    iapply (valHasType_lookup_zip_reverse args' argVars vs ρ' TinyML.TyCtx.empty x x' sx σ
      (by rw [hfst]; exact hlen_nv)
      (by rw [hfst]; exact hlen_nvl)
      (by rw [hfst]; exact hmem)
      hΓ hargVars_lookup)
    rw [hsnd]
    iassumption
  have hbody : st'.sl W ρ' ∗ (Bindings.typedScope W Gbody Bbody Γ' γg_body γ_body ∗ Q) ⊢
      |==> ∃ v, Φ v := by
    refine compileGhostExpr_correct W Gf hwf body Gbody Bbody Γ' γg_body γ_body
      hag hgagree_body hgwf_body hagree_body hbwf_body hGf
      (VerifM.eval.decls_grow ρ' hcompile) ?_
    intro v st'' ρ'' t hΨ ht_wf ht_eval
    obtain ⟨_, _, hΨ⟩ := hΨ
    simp only [checkRet] at hΨ
    by_cases hsub : body.ty = retTy
    case neg =>
      simp [hsub] at hΨ
      exact (VerifM.eval_fatal (VerifM.eval_bind hΨ)).elim
    simp [hsub] at hΨ
    have hΨ' := VerifM.eval_ret hΨ
    dsimp only at hΨ'
    rw [← ht_eval]
    refine (show st''.sl W ρ'' ∗ TinyML.ValHasType W (t.eval ρ'') body.ty ∗ Q ⊢
        st''.sl W ρ'' ∗ Q ∗
          ((TinyML.ValHasType W (t.eval ρ'') retTy -∗ Φ (t.eval ρ'')) -∗
            Φ (t.eval ρ'')) from ?_).trans (hΨ' _ ht_wf)
    iintro ⟨Howns', Hty, HQ'⟩
    iframe Howns' HQ'
    iintro Hwand
    iapply Hwand
    rw [← hsub]
    iexact Hty
  iapply hbody
  iframe Howns
  unfold Bindings.typedScope
  isplitl []
  · isplitl []
    · iapply hts_g
      iexact Hgvals
    · iapply hts
      iexact Hvals
  · iexact HQ

omit [MicaGS HasLC.hasLC Sig] in
private theorem constTerms_eval {ρ : Env} :
    ∀ {vars : List FOL.Const} {vals : List Runtime.Val},
      List.Forall₂ (fun av val => ρ.consts .value av.name = val) vars vals →
      Terms.Eval ρ (vars.map fun c => Term.const (.uninterpreted c.name .value)) vals
  | [], _, h => by cases h; exact .nil
  | a :: rest, _, h => by
    cases h with
    | cons hhead htail =>
      exact .cons (by simpa [Term.eval, Const.denote] using hhead) (constTerms_eval htail)

omit [MicaGS HasLC.hasLC Sig] in
/-- Argument constants keep their values as the verifier state grows. -/
private theorem constLookups_env_agree {Δ : Signature} {ρ ρ' : Env}
    (hagree : Env.agreeOn Δ ρ ρ') :
    ∀ {vars : List FOL.Const} {vals : List Runtime.Val},
      (∀ v ∈ vars, v ∈ Δ.consts) → (∀ v ∈ vars, v.sort = .value) →
      List.Forall₂ (fun av val => ρ.consts .value av.name = val) vars vals →
      List.Forall₂ (fun av val => ρ'.consts .value av.name = val) vars vals
  | [], _, _, _, h => by cases h; exact .nil
  | a :: rest, _, hmem, hsort, h => by
    cases h with
    | cons hhead htail =>
      refine .cons ?_ (constLookups_env_agree hagree
        (fun c hc => hmem c (.tail _ hc)) (fun c hc => hsort c (.tail _ hc)) htail)
      have hc := hagree.2.1 a (hmem a (.head _))
      rw [hsort a (.head _)] at hc
      rw [← hc]; exact hhead

/-- One rank of a ghost declaration's guarantee. `bodyGf` installs the ghost
    functions the body may call, which is where the recursive occurrence comes
    from. -/
private theorem ValDecl.checkGhostRank_correct (W : TinyML.World) (hwf : W.wf)
    (argTys : List TinyML.Typ) (retTy : TinyML.Typ) (s : Spec TinyML.Typ) (body : Expr)
    (argNames : List String)
    (μ : List Runtime.Val → List Runtime.Val → Nat) (k : Nat)
    (bodyGf : List FOL.Const → List FOL.Const → VerifM GhostFns)
    (hswf : s.wfIn W.Δ_spec) (hslen : s.args.length = argTys.length)
    (hlen_args : argNames.length = argTys.length)
    {st : TransState} {ρ : Env} (hag : W.agrees st.decls ρ) (howns : st.owns = [])
    (himpl : VerifM.eval (Spec.implement W.Δ_spec argTys s (fun argVars ghostVars => do
          let Gf' ← bodyGf argVars ghostVars
          let se ← compileGhostExpr W.Θ W.Δ_spec Gf'
            (ghostBodyGhosts (s.ghost.map Prod.fst) ghostVars)
            (ghostBodyArgs argNames argVars (s.ghost.map Prod.fst))
            (ghostBodyTyCtx argNames argTys s.ghost) body
          checkRet retTy body.ty
          pure se)) st ρ (fun _ _ _ => True))
    (hbodyGf : ∀ (vs gs : List Runtime.Val) (argVars ghostVars : List FOL.Const)
        (st' : TransState) (ρ' : Env) (Ψ : GhostFns → TransState → Env → Prop),
      st.decls.Subset st'.decls → Env.agreeOn st.decls ρ ρ' →
      (∀ v ∈ argVars, v ∈ st'.decls.consts) → (∀ v ∈ argVars, v.sort = .value) →
      List.Forall₂ (fun av val => ρ'.consts .value av.name = val) argVars vs →
      (∀ v ∈ ghostVars, v ∈ st'.decls.consts) → (∀ v ∈ ghostVars, v.sort = .value) →
      List.Forall₂ (fun gv val => ρ'.consts .value gv.name = val) ghostVars gs →
      vs.length = argTys.length → gs.length = s.ghost.length → μ vs gs < k →
      VerifM.eval (bodyGf argVars ghostVars) st' ρ' Ψ →
      ∃ Gf' st'' ρ'', st'.decls.Subset st''.decls ∧ Env.agreeOn st'.decls ρ' ρ'' ∧
        (st'.sl W ρ' ⊢ st''.sl W ρ'') ∧ GhostFns.wellTyped W st''.decls ρ'' Gf' ∧
        Ψ Gf' st'' ρ'') :
    ⊢ Spec.isGhostPrecondForAt W (TinyML.ValHasType W) argTys retTy s μ k := by
  unfold Spec.isGhostPrecondForAt
  istart
  imodintro
  iintro %ρ_call %Φ %vs %gs %hagree_call %hlen_vs %hlen_gs %hrank #Hvals #Hgvals Hpred
  ihave Hwand := Spec.implement_correct W argTys retTy s _ st ρ vs gs Φ
    iprop(TinyML.ValsHaveTypes W vs argTys -∗
      TinyML.ValsHaveTypes W gs (s.ghost.map Prod.snd) -∗ |==> ∃ v, Φ v)
    hslen (by omega) hswf hwf hag himpl
    (fun argVars ghostVars st' ρ' Q hst_sub hρ_agree hargVars_mem hargVars_sort hargVars_lookup
        hghostVars_mem hghostVars_sort hghostVars_lookup hbody_eval => by
      obtain ⟨Gf', st'', ρ'', hst_sub', hρ_agree', hsl_step, hGf', hrest⟩ :=
        hbodyGf vs gs argVars ghostVars st' ρ' _ hst_sub hρ_agree
          hargVars_mem hargVars_sort hargVars_lookup
          hghostVars_mem hghostVars_sort hghostVars_lookup hlen_vs hlen_gs hrank
          (VerifM.eval_bind hbody_eval)
      iintro ⟨Hsl, HQ⟩ Htyped Hgtyped
      iapply (ValDecl.checkGhostBody_correct W Gf' hwf s argTys retTy body argNames vs gs Φ
        (hag.step (hst_sub.trans hst_sub') (Env.agreeOn_trans hρ_agree
          (Env.agreeOn_mono hst_sub hρ_agree')))
        hGf' hlen_args
        (fun v hv => hst_sub'.consts v (hargVars_mem v hv)) hargVars_sort
        (constLookups_env_agree hρ_agree' hargVars_mem hargVars_sort hargVars_lookup)
        (fun v hv => hst_sub'.consts v (hghostVars_mem v hv)) hghostVars_sort
        (constLookups_env_agree hρ_agree' hghostVars_mem hghostVars_sort hghostVars_lookup)
        hrest)
      isplitl [Hsl]
      · iapply hsl_step
        iexact Hsl
      · isplitl [Htyped]
        · iexact Htyped
        · isplitl [Hgtyped]
          · iexact Hgtyped
          · iexact HQ) $$ [Hpred]
  · isplitl []
    · simp [TransState.sl, howns]
      iempintro
    · isplitl []
      · iexact Hvals
      · isplitl []
        · iexact Hgvals
        · have hlen_call : s.allArgs.length ≤ (vs ++ gs).length := by
            simp [Spec.allArgs]; omega
          iapply (PredTrans.apply_env_agree (TinyML.ValHasType W)
            (ρ := Spec.argsEnv ρ_call s.allArgs (vs ++ gs))
            (ρ' := Spec.argsEnv W.ρ_spec s.allArgs (vs ++ gs)) hswf
            (Spec.argsEnv_agreeOn (Δ := W.Δ_spec) (ρ₁ := ρ_call) (ρ₂ := W.ρ_spec)
              (Env.agreeOn_symm hagree_call) s.allArgs (vs ++ gs) hlen_call))
          iexact Hpred
  ispecialize Hwand $$ [Hvals]
  · iexact Hvals
  ispecialize Hwand $$ [Hgvals]
  · iexact Hgvals
  iexact Hwand

/-- The recursion is justified by strong induction on the rank the declaration's
    measure gives its arguments. -/
theorem ValDecl.checkGhost_correct (W : TinyML.World) (Gf : GhostFns) (hwf : W.wf)
    (d : Typed.ValDecl)
    {st : TransState} {ρ : Env} (hag : W.agrees st.decls ρ)
    (hGf : GhostFns.wellTyped W st.decls ρ Gf)
    {Q : (TinyML.Var × GhostFns.Entry) → TransState → Env → Prop}
    (heval : VerifM.eval (ValDecl.checkGhost W.Θ W.Δ_spec Gf d) st ρ Q) :
    ∃ entry, GhostFns.wellTyped W st.decls ρ (entry :: Gf) ∧ Q entry st ρ := by
  simp only [ValDecl.checkGhost] at heval
  obtain ⟨f, hname, heval⟩ := VerifM.eval_bind_expectSome heval
  cases hbody : d.body with
  | fix self args retTy spec body =>
    cases spec with
    | none => simp only [hbody] at heval; exact (VerifM.eval_fatal heval).elim
    | some s =>
    simp only [hbody] at heval
    cases hext : extractArgNames args s.args with
    | error msg => simp only [hext] at heval; exact (VerifM.eval_fatal heval).elim
    | ok argNames =>
    simp only [hext] at heval
    cases hcheck : Spec.checkWf s W.Δ_spec with
    | error msg => simp only [hcheck] at heval; exact (VerifM.eval_fatal heval).elim
    | ok u =>
    cases u
    simp only [hcheck] at heval
    obtain ⟨hargNames_len, hargs_len, _⟩ := extractArgNames_spec hext
    have hswf : s.wfIn W.Δ_spec := Spec.checkWf_ok hcheck
    have hslen : s.args.length = (args.map Binder.WithTypeVars.ty).length := by
      simpa using hargs_len.symm
    have hlen_args : argNames.length = (args.map Binder.WithTypeVars.ty).length := by
      simpa using hargNames_len.trans hargs_len.symm
    obtain ⟨himpl_seq, hcont⟩ := VerifM.eval_seq heval
    have himpl := VerifM.eval_persist (VerifM.eval_bind himpl_seq)
    have hag' : W.agrees (TransState.persist st).decls ρ := by simpa using hag
    have hGf' : GhostFns.wellTyped W (TransState.persist st).decls ρ Gf := by simpa using hGf
    refine ⟨(f, ⟨.arrow (args.map Binder.WithTypeVars.ty) retTy (some s), none⟩), ?_,
      VerifM.eval_ret hcont⟩
    intro η f' argTys' retTy' s' guard' hlookup
    by_cases hf : f' = f
    · subst hf
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq,
        GhostFns.Entry.mk.injEq] at hlookup
      obtain ⟨hty, hguard⟩ := hlookup
      cases hty; cases hguard
      have hpersist_owns : (TransState.persist st).owns = [] := rfl
      cases hself : self.name with
      | none =>
        refine Spec.isGhostPrecondFor.induction_eta (fun _ _ => 0) ?_ η
        intro k η' _
        refine ValDecl.checkGhostRank_correct { W with eta := η' } (hwf.eta η') _ retTy s body
          argNames _ k _ hswf hslen hlen_args (hag'.eta η') hpersist_owns himpl ?_
        intro vs gs argVars ghostVars st₁ ρ₁ Ψ hst_sub hρ_agree _ _ _ _ _ _ _ _ _ hev
        simp only [ValDecl.ghostSelf, hself] at hev
        exact ⟨Gf, st₁, ρ₁, Signature.Subset.refl _, Env.agreeOn_refl, .rfl,
          GhostFns.wellTyped.eta
            (hGf'.step hst_sub hρ_agree (VerifM.eval.wf hev).namesDisjoint),
          VerifM.eval_ret hev⟩
      | some g =>
        cases hdec : d.decreases with
        | none =>
          refine Spec.isGhostPrecondFor.induction_eta (fun _ _ => 0) ?_ η
          intro k η' _
          refine ValDecl.checkGhostRank_correct { W with eta := η' } (hwf.eta η') _ retTy s body
            argNames _ k _ hswf hslen hlen_args (hag'.eta η') hpersist_owns himpl ?_
          intro vs gs argVars ghostVars st₁ ρ₁ Ψ _ _ _ _ _ _ _ _ _ _ _ hev
          simp only [ValDecl.ghostSelf, hself, hdec] at hev
          exact (VerifM.eval_fatal hev).elim
        | some measure =>
          refine Spec.isGhostPrecondFor.induction_eta (measure.denote s W.ρ_spec) ?_ η
          intro k η' ih
          refine ValDecl.checkGhostRank_correct { W with eta := η' } (hwf.eta η') _ retTy s body
            argNames _ k _ hswf hslen hlen_args (hag'.eta η') hpersist_owns himpl ?_
          intro vs gs argVars ghostVars st₁ ρ₁ Ψ hst_sub hρ_agree hargVars_mem hargVars_sort
            hargVars_lookup hghostVars_mem hghostVars_sort hghostVars_lookup hlen_vs hlen_gs
            hrank hev
          have hag₁ : W.agrees st₁.decls ρ₁ := hag'.step hst_sub hρ_agree
          have hlen_call : s.allArgs.length ≤ (vs ++ gs).length := by
            simp [Spec.allArgs]; omega
          have hlen_terms : s.allArgs.length =
              ((argVars ++ ghostVars).map fun c =>
                (Term.const (.uninterpreted c.name .value) : Term .value)).length := by
            have h₁ := hargVars_lookup.length_eq
            have h₂ := hghostVars_lookup.length_eq
            simp [Spec.allArgs]; omega
          have hterms_eval : Terms.Eval ρ₁
              ((argVars ++ ghostVars).map fun c =>
                (Term.const (.uninterpreted c.name .value) : Term .value)) (vs ++ gs) := by
            rw [List.map_append]
            exact List.rel_append (constTerms_eval hargVars_lookup)
              (constTerms_eval hghostVars_lookup)
          simp only [ValDecl.ghostSelf, hself, hdec, GhostFns.Guard.declare] at hev
          cases hmwf : measure.term.checkWf (W.Δ_spec.declVars (Spec.argVars s.allArgs)) with
          | error msg => rw [hmwf] at hev; exact (VerifM.eval_fatal hev).elim
          | ok u =>
          cases u
          rw [hmwf] at hev
          have hmeasure_wf : measure.term.wfIn (W.Δ_spec.declVars (Spec.argVars s.allArgs)) :=
            Term.checkWf_ok hmwf
          have hev := VerifM.eval_decls (VerifM.eval_bind hev)
          set m := measure.term.subst (Spec.argSubst Subst.id s.allArgs
            ((argVars ++ ghostVars).map fun c =>
              (Term.const (.uninterpreted c.name .value) : Term .value))) with hm_def
          cases hmwf₂ : m.checkWf st₁.decls with
          | error msg => rw [hmwf₂] at hev; exact (VerifM.eval_fatal hev).elim
          | ok u =>
          cases u
          rw [hmwf₂] at hev
          have hm_wf : m.wfIn st₁.decls := Term.checkWf_ok hmwf₂
          have hstwf : st₁.decls.wf := (VerifM.eval.wf hev).namesDisjoint
          have hownsWf := (VerifM.eval.wf hev).ownsWf
          set rv := st₁.freshConst (some "rank") .int with hrv_def
          have hfresh : rv.name ∉ st₁.decls.allNames := st₁.freshConst_fresh (some "rank") .int
          have hev := VerifM.eval_decl (VerifM.eval_bind hev) (Term.eval ρ₁ m)
          set st₂ : TransState := { st₁ with decls := st₁.decls.addConst rv } with hst₂_def
          set ρ₂ := ρ₁.updateConst .int rv.name (Term.eval ρ₁ m) with hρ₂_def
          have hsub₂ : st₁.decls.Subset st₂.decls := Signature.Subset.subset_addConst _ _
          have hagree₂ : Env.agreeOn st₁.decls ρ₁ ρ₂ := Env.agreeOn_update_fresh_const hfresh
          have hφ_wf : (Formula.eq .int (.const (.uninterpreted rv.name .int)) m).wfIn st₂.decls :=
            Formula.eq_wfIn_addConst_of_fresh (Δ := st₁.decls) (c := rv) hstwf hm_wf hfresh
          have hφ_eval : (Formula.eq .int (.const (.uninterpreted rv.name .int)) m).eval ρ₂ := by
            simp only [Formula.eval, Term.eval_const_updateConst, hρ₂_def]
            exact Term.eval_env_agree hm_wf hagree₂
          have hev := VerifM.eval_assumePure (VerifM.eval_bind hev) hφ_wf hφ_eval
          have hr_wf : (Term.const (.uninterpreted rv.name .int) : Term .int).wfIn st₂.decls :=
            Term.const_wfIn_addConst_of_fresh (Δ := st₁.decls) (c := rv) hstwf hfresh
          have hrank_eq : (Term.eval ρ₂ (Term.const (.uninterpreted rv.name .int))).toNat =
              measure.denote s W.ρ_spec vs gs := by
            simp only [Term.eval_const_updateConst, hρ₂_def, Typed.Measure.denote]
            rw [Spec.eval_argSubst (Δ := W.Δ_spec) hlen_terms hterms_eval measure.term hmeasure_wf,
              Term.eval_env_agree hmeasure_wf (Spec.argsEnv_agreeOn (Δ := W.Δ_spec)
                (Env.agreeOn_symm hag₁.agree) s.allArgs (vs ++ gs) hlen_call)]
          have hΨ := VerifM.eval_ret hev
          refine ⟨_, _, ρ₂, ?_, hagree₂, ?_, ?_, hΨ⟩
          · exact hsub₂
          · exact (SpatialContext.interp_env_agree _ hownsWf hagree₂).1
          intro η'' f'' argTys'' retTy'' s'' guard'' hlookup''
          by_cases hg : f'' = g
          · subst hg
            simp only [List.lookup, beq_self_eq_true, Option.some.injEq,
              GhostFns.Entry.mk.injEq] at hlookup''
            obtain ⟨hty'', hguard''⟩ := hlookup''
            cases hty''; cases hguard''
            refine ⟨hr_wf, hmeasure_wf, ?_⟩
            rw [hrank_eq]
            exact ih _ hrank η''
          · have hne : (f'' == g) = false := by simpa using hg
            rw [List.lookup, hne] at hlookup''
            exact GhostFns.wellTyped.eta
              (hGf'.step (hst_sub.trans hsub₂) (Env.agreeOn_trans hρ_agree
                (Env.agreeOn_mono hst_sub hagree₂)) (Signature.wf_addConst hstwf hfresh))
              η'' f'' argTys'' retTy'' s'' guard'' hlookup''
    · have hne : (f' == f) = false := by simpa using hf
      have hlookup' : Gf.lookup f' = some ⟨.arrow argTys' retTy' (some s'), guard'⟩ := by
        rw [List.lookup, hne] at hlookup; exact hlookup
      exact hGf η f' argTys' retTy' s' guard' hlookup'
  | _ => simp only [hbody] at heval; exact (VerifM.eval_fatal heval).elim

end Declarations

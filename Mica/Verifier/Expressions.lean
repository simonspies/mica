import Mica.TinyML.Typed
import Mica.TinyML.Typing
import Mica.TinyML.OpSem
import Mica.TinyML.WeakestPre
import Mica.Verifier.Monad
import Mica.Verifier.Assertions
import Mica.Verifier.PredicateTransformers
import Mica.Verifier.Specifications
import Mica.Verifier.Utils
import Mica.Engine.Driver
import Mica.Base.Fresh
import Mathlib.Data.Finmap

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

@[simp] theorem vtailN_eval (t : Term .vallist) (ρ : Env) :
    ∀ n, (vtailN t n).eval ρ = List.drop n (t.eval ρ)
  | 0 => by simp [vtailN]
  | n + 1 => by
    simp only [vtailN, Term.eval, UnOp.eval, vtailN_eval t ρ n]
    rw [List.tail_drop]

theorem vhead_vtailN_eval {vs : List Runtime.Val} {w : Runtime.Val} {n : Nat}
    (h : vs[n]? = some w) (t : Term .vallist) (ρ : Env) (ht : t.eval ρ = vs) :
    (Term.unop .vhead (vtailN t n)).eval ρ = w := by
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

theorem compileUnop_eval {op : TinyML.UnOp} {s : Term .value} {ρ : Env}
    {v w : Runtime.Val} {t : Term .value}
    (hs : s.eval ρ = v) (heval : TinyML.evalUnOp op v = some w)
    (hcomp : compileUnop op s = some t) :
    t.eval ρ = w := by
  subst hs
  cases op with
  | proj n =>
    simp only [compileUnop, Option.some.injEq] at hcomp; subst hcomp
    cases h : s.eval ρ <;> simp_all [TinyML.evalUnOp]
    exact vhead_vtailN_eval heval _ ρ (by simp [Term.eval, UnOp.eval, h])
  | neg | not =>
    simp only [compileUnop, Option.some.injEq] at hcomp
    subst hcomp
    cases h : s.eval ρ <;>
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
theorem compileOp_eval {op : TinyML.BinOp} {sl sr : Term .value} {ρ : Env}
    {v1 v2 w : Runtime.Val} {t : Term .value}
    (hsl : sl.eval ρ = v1) (hsr : sr.eval ρ = v2)
    (heval : TinyML.evalBinOp op v1 v2 = some w)
    (hcomp : compileOp op sl sr = some t) :
    t.eval ρ = w := by
  subst hsl hsr
  cases op <;>
    simp only [compileOp, Option.some.injEq] at hcomp <;>
    (try simp at hcomp) <;>
    subst hcomp <;>
    (cases h1 : sl.eval ρ <;> cases h2 : sr.eval ρ) <;>
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
        let sl ← compile Θ S B Γ l
        let sr ← compile Θ S B Γ r
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
          VerifM.assume (Formula.eq .value (.const (.uninterpreted x'.name .value)) se)
          compile Θ (Finmap.erase x S) ((x, x') :: B) (Γ.extend x e.ty) body
    | .ifThenElse cond thn els ty => do
        let sc ← compile Θ S B Γ cond
        VerifM.expectEq "if branch type annotation mismatch" thn.ty ty
        VerifM.expectEq "if branch type annotation mismatch" els.ty ty
        let branch ← VerifM.all [true, false]
        if branch then do
          VerifM.assume (.not (.eq .value sc (.unop .ofBool (.const (.b false)))))
          compile Θ S B Γ thn
        else do
          VerifM.assume (.eq .value sc (.unop .ofBool (.const (.b false))))
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
    | .app _ _ _ | .fix _ _ _ _ | .ref _ | .deref _ _ | .store _ _ => VerifM.fatal "unsupported expression"

  /-- Compile a single match branch: assume the scrutinee is `mkInj i n payload`, then compile the body. -/
  def compileBranch (Θ : TinyML.TypeEnv) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
      (sc : Term .value) (n : Nat) (i : Nat) (ty_i : TinyML.Typ)
      : Binder × Expr → VerifM (Term .value)
    | (binder, body) => do
        VerifM.expectEq "match binder type annotation mismatch" binder.ty ty_i
        let xv ← VerifM.decl binder.name .value
        VerifM.assume (.eq .value sc (.unop (.mkInj i n) (.const (.uninterpreted xv.name .value))))
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



/-! ### Helper lemmas for match compilation -/

/-- Applying a single-argument lambda `(fun b -> body)` to a value reduces to substituting. -/
theorem wp_app_lambda_single {b : Runtime.Binder} {body : Runtime.Expr} {v : Runtime.Val}
    {Φ : Runtime.Val → Prop} :
    wp (body.subst (Runtime.Subst.id.update' b v)) Φ →
    wp (.app (.fix .none [b] body) [.val v]) Φ := by
  intro h
  apply wp.app
  simp only [wps_cons, wps_nil]
  apply wp.val; apply wp.func
  exact (wp.fix Φ body (fun vs => vs = [v]) (by
    intro _ vs hvs; subst hvs
    simp only [Runtime.Subst.updateAll'_cons, Runtime.Subst.updateAll'_nil_left,
               Runtime.Subst.update']
    exact h)) [v] rfl

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

/-! ### Correctness -/

mutual

theorem compile_correct (Θ : TinyML.TypeEnv) (e : Expr) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) (st : TransState) (ρ : Env) (γ : Runtime.Subst)
    (Ψ : Term .value → TransState → Env → Prop) (Φ : Runtime.Val → Prop) :
    VerifM.eval (compile Θ S B Γ e) st ρ Ψ →
    B.agreeOnLinked ρ γ →
    B.wf st.decls →
    B.typedSubst Θ Γ γ →
    S.satisfiedBy Θ γ →
    S.wfIn Signature.empty →
    (∀ v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls → Term.eval ρ' se = v →
      TinyML.ValHasType Θ v e.ty → Φ v) →
    wp (e.runtime.subst γ) Φ := by
  intro heval hagree hbwf hts hspec hSwf hpost
  cases e with
  | const c =>
    cases c with
    | int n =>
      simp only [compile] at heval
      simp only [Expr.runtime, TinyML.Const.runtime, Runtime.Expr.subst_val]; apply wp.val
      obtain heval := VerifM.eval_ret heval
      simp only [Expr.ty, Const.ty] at hpost
      exact hpost (.int n) ρ st _ heval
        (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
        (by simp [Term.eval, UnOp.eval, Const.denote])
        (.int n)
    | bool b =>
      simp only [compile] at heval
      simp only [Expr.runtime, TinyML.Const.runtime, Runtime.Expr.subst_val]; apply wp.val
      obtain heval := VerifM.eval_ret heval
      simp only [Expr.ty, Const.ty] at hpost
      exact hpost (.bool b) ρ st _ heval
        (by simp [Term.wfIn, Const.wfIn, UnOp.wfIn])
        (by simp [Term.eval, UnOp.eval, Const.denote])
        (.bool b)
    | unit =>
      simp only [compile] at heval
      simp only [Expr.runtime, TinyML.Const.runtime, Runtime.Expr.subst_val]; apply wp.val
      obtain heval := VerifM.eval_ret heval
      simp only [Expr.ty, Const.ty] at hpost
      exact hpost .unit ρ st _ heval
        (by simp [Term.wfIn, Const.wfIn])
        (by simp [Term.eval])
        .unit
  | var x vty =>
    simp only [compile] at heval
    obtain ⟨x', hbind, heval⟩ := VerifM.eval_bind_expectSome heval
    by_cases hcheck : (Γ x |>.getD .value) = vty
    · obtain ⟨_, hcont⟩ := VerifM.eval_bind_expectEq heval
      unfold Expr.runtime; simp only [Runtime.Expr.subst]
      obtain ⟨hsort, hγ⟩ := hagree x x' hbind
      rw [hγ]; simp
      apply wp.val
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
      have htyping : TinyML.ValHasType Θ (ρ.consts .value x'.name) vty := by
        rw [← hcheck]
        cases hΓ : Γ x with
        | none => exact .any
        | some t =>
          obtain ⟨w, hw, hwt⟩ := hts x x' t hbind hΓ
          rw [hγ] at hw
          exact (Option.some.inj hw) ▸ hwt
      exact hpost _ ρ st _ heval hwfv (by simp [Term.eval, Const.denote]) htyping
    · exact False.elim (hcheck (VerifM.eval_bind_expectEq heval).1)
  | inj tag arity payload =>
    unfold Expr.runtime; simp only [Runtime.Expr.subst]
    apply wp.inj
    simp only [compile] at heval
    by_cases htag : tag ≥ arity
    · simp [htag] at heval; exact (VerifM.eval_fatal heval).elim
    · push_neg at htag
      simp [show ¬(tag ≥ arity) from Nat.not_le.mpr htag] at heval
      have heval_p : (compile Θ S B Γ payload).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
      refine compile_correct Θ payload S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_p) hagree hbwf hts hspec hSwf ?_
      intro v_p ρ_p st_p se_p hΨ_p hse_wf_p heval_se_p htype_p
      obtain ⟨hdecls_p, hagreeOn_p, hΨ_p⟩ := hΨ_p
      obtain hΨ_p := VerifM.eval_ret hΨ_p
      simp only [Expr.ty] at hpost
      exact hpost (.inj tag arity v_p) ρ_p st_p _ hΨ_p
        (by simp only [Term.wfIn]; exact ⟨trivial, hse_wf_p⟩)
        (by simp [Term.eval, UnOp.eval, heval_se_p])
        (by
          let ts := (List.replicate arity TinyML.Typ.empty).set tag payload.ty
          have hlen_ts : ts.length = arity := by simp [ts]
          have : TinyML.ValHasType Θ (.inj tag ts.length v_p) (.sum ts) :=
            .inj (ts := ts) (by simp [ts, htag]) htype_p
          rwa [hlen_ts] at this)
  | cast e ty =>
    simp only [Expr.ty] at hpost
    simp only [compile] at heval
    have heval_e : (compile Θ S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    simp [Expr.runtime]
    refine compile_correct Θ e S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hts hspec hSwf ?_
    intro v ρ' st' se hΨ hse_wf heval_se htype_v
    obtain ⟨_, _, hΨ⟩ := hΨ
    cases hsub : TinyML.Typ.sub Θ e.ty ty
    · simp [hsub] at hΨ
      exact (VerifM.eval_fatal hΨ).elim
    · simp [hsub] at hΨ
      obtain hΨ := VerifM.eval_ret hΨ
      have hsub' : TinyML.Typ.Sub Θ e.ty ty := TinyML.Typ.sub_sound hsub
      exact hpost v ρ' st' se hΨ hse_wf heval_se (TinyML.ValHasType_sub htype_v hsub')
  | assert e =>
    unfold Expr.runtime; simp only [Runtime.Expr.subst]
    apply wp.assert
    simp only [compile] at heval
    have heval_e : (compile Θ S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compile_correct Θ e S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hts hspec hSwf ?_
    intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se _
    obtain ⟨_, _, hΨ_e⟩ := hΨ_e
    let φ := Formula.eq .bool (Term.unop .toBool se) (Term.const (.b true))
    have hwf_φ : φ.wfIn st₁.decls := by
      simp only [φ, Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, and_true, true_and]; exact hse_wf
    have heval_assert : (VerifM.assert φ).eval st₁ ρ_e _ := VerifM.eval_bind _ _ _ _ hΨ_e
    obtain ⟨_, hcont⟩ := VerifM.eval_assert heval_assert hwf_φ
    have hΨ_pure := VerifM.eval_ret hcont
    intro _
    simp only [Expr.ty] at hpost
    exact hpost .unit ρ_e st₁ (Term.const .unit) hΨ_pure
      trivial
      (by simp [Term.eval])
      .unit
  | fix _ _ _ _ | ref _ | deref _ _ | store _ _ =>
    simp only [compile] at heval
    exact (VerifM.eval_fatal heval).elim
  | unop op e uty =>
    unfold Expr.runtime; simp only [Runtime.Expr.subst]
    apply wp.unop
    simp only [compile] at heval
    have heval_e : (compile Θ S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compile_correct Θ e S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hts hspec hSwf ?_
    intro v_e ρ_e st₁ se hΨ_e hse_wf heval_se htype_e
    obtain ⟨_, _, hΨ_e⟩ := hΨ_e
    obtain ⟨ty, htypeOf, hΨ_e⟩ := VerifM.eval_bind_expectSome hΨ_e
    obtain ⟨hty_eq, hΨ_e⟩ := VerifM.eval_bind_expectEq hΨ_e
    obtain ⟨t, hcompUnop, hΨ_e⟩ := VerifM.eval_bind_expectSome hΨ_e
    obtain hΨ_e := VerifM.eval_ret hΨ_e
    obtain ⟨w, heval_op, hwt⟩ := evalUnOp_typed htypeOf htype_e
    have ht_eval : t.eval ρ_e = w :=
      compileUnop_eval heval_se heval_op hcompUnop
    simp only [Expr.ty] at hpost
    exact ⟨w, heval_op, hpost w ρ_e st₁ t hΨ_e
      (compileUnop_wfIn hse_wf hcompUnop) ht_eval (hty_eq ▸ hwt)⟩
  | binop op l r bty =>
    unfold Expr.runtime; simp only [Runtime.Expr.subst]
    apply wp.binop
    simp only [compile] at heval
    have heval_l : (compile Θ S B Γ l).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compile_correct Θ l S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_l) hagree hbwf hts hspec hSwf ?_
    intro vl ρ_l st₁ sl hΨ_l hsl_wf heval_l htyl
    obtain ⟨hdecls_l, hagreeOn_l, hΨ_l⟩ := hΨ_l
    have hagree_l : B.agreeOnLinked ρ_l γ :=
      Bindings.agreeOnLinked_env_agree hagree hagreeOn_l hbwf
    have hbwf_l : B.wf st₁.decls := fun p hp => hdecls_l.consts _ (hbwf p hp)
    have heval_r : (compile Θ S B Γ r).eval st₁ ρ_l _ := VerifM.eval_bind _ _ _ _ hΨ_l
    refine compile_correct Θ r S B Γ st₁ ρ_l γ _ _ (VerifM.eval.decls_grow ρ_l heval_r) hagree_l hbwf_l hts hspec hSwf ?_
    intro vr ρ_r st₂ sr hΨ_r hsr_wf heval_r htyr
    obtain ⟨hdecls_r, hagreeOn_r, hΨ_r⟩ := hΨ_r
    obtain ⟨ty, htypeOf, hΨ_r⟩ := VerifM.eval_bind_expectSome hΨ_r
    obtain ⟨hty_eq, hΨ_r'⟩ := VerifM.eval_bind_expectEq hΨ_r
    simp only [Expr.ty] at hpost
    /- Split on whether op is division -/
    by_cases hdivmod : op = .div ∨ op = .mod
    · -- Division or modulo: both have the non-zero divisor assertion
      have hΨ_div :
            (do
              let i t := Term.unop UnOp.toInt t
              let fol_op := if op == TinyML.BinOp.div then BinOp.div else BinOp.mod
              VerifM.assert (.not (.eq .int (i sr) (.const (.i 0))))
              pure (Term.unop .ofInt (Term.binop fol_op (i sl) (i sr)))).eval st₂ ρ_r Ψ := by
        simpa [hdivmod] using hΨ_r'
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
              simp only [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, and_true, true_and]; exact hsr_wf
            have heval_assert := VerifM.eval_bind _ _ _ _ hΨ_div
            have ⟨hne_zero, hΨ_post⟩ := VerifM.eval_assert heval_assert hassert_wf
            simp [Formula.eval, Term.eval, Const.denote] at hne_zero
            have hsr_eval : sr.eval ρ_r = Runtime.Val.int b := heval_r
            rw [hsr_eval] at hne_zero
            simp at hne_zero
            obtain hΨ_post := VerifM.eval_ret hΨ_post
            have hsl_ρ_r : sl.eval ρ_r = Runtime.Val.int a := by
              rw [Term.eval_env_agree hsl_wf (Env.agreeOn_symm hagreeOn_r)]; exact heval_l
            have hty_int : ty = .int := by
              rw [hlty, hrty] at htypeOf
              simpa [TinyML.BinOp.typeOf] using htypeOf.symm
            have hbty : bty = .int := by
              exact hty_eq.symm.trans hty_int
            have hwf_bin : (Term.unop .ofInt (Term.binop BinOp.div (Term.unop .toInt sl) (Term.unop .toInt sr))).wfIn st₂.decls := by
              simp only [Term.wfIn, BinOp.wfIn, UnOp.wfIn, true_and]
              exact ⟨Term.wfIn_mono sl hsl_wf hdecls_r (VerifM.eval.wf hΨ_div).namesDisjoint, hsr_wf⟩
            have hΨ_post' : Ψ (Term.unop .ofInt (Term.binop BinOp.div (Term.unop .toInt sl) (Term.unop .toInt sr))) st₂ ρ_r := by
              simpa using hΨ_post
            exact ⟨.int (a / b), by simp [TinyML.evalBinOp, hne_zero],
              hpost (.int (a / b)) ρ_r st₂ _ hΨ_post' hwf_bin
                (by simp [Term.eval, UnOp.eval, BinOp.eval, hsl_ρ_r, hsr_eval])
                (hbty ▸ .int _)⟩
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
              simp only [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, and_true, true_and]; exact hsr_wf
            have heval_assert := VerifM.eval_bind _ _ _ _ hΨ_div
            have ⟨hne_zero, hΨ_post⟩ := VerifM.eval_assert heval_assert hassert_wf
            simp [Formula.eval, Term.eval, Const.denote] at hne_zero
            have hsr_eval : sr.eval ρ_r = Runtime.Val.int b := heval_r
            rw [hsr_eval] at hne_zero
            simp at hne_zero
            obtain hΨ_post := VerifM.eval_ret hΨ_post
            have hsl_ρ_r : sl.eval ρ_r = Runtime.Val.int a := by
              rw [Term.eval_env_agree hsl_wf (Env.agreeOn_symm hagreeOn_r)]; exact heval_l
            have hty_int : ty = .int := by
              rw [hlty, hrty] at htypeOf
              simpa [TinyML.BinOp.typeOf] using htypeOf.symm
            have hbty : bty = .int := by
              exact hty_eq.symm.trans hty_int
            have hwf_bin : (Term.unop .ofInt (Term.binop BinOp.mod (Term.unop .toInt sl) (Term.unop .toInt sr))).wfIn st₂.decls := by
              simp only [Term.wfIn, BinOp.wfIn, UnOp.wfIn, true_and]
              exact ⟨Term.wfIn_mono sl hsl_wf hdecls_r (VerifM.eval.wf hΨ_div).namesDisjoint, hsr_wf⟩
            have hΨ_post' : Ψ (Term.unop .ofInt (Term.binop BinOp.mod (Term.unop .toInt sl) (Term.unop .toInt sr))) st₂ ρ_r := by
              simpa using hΨ_post
            exact ⟨.int (a % b), by simp [TinyML.evalBinOp, hne_zero],
              hpost (.int (a % b)) ρ_r st₂ _ hΨ_post' hwf_bin
                (by simp [Term.eval, UnOp.eval, BinOp.eval, hsl_ρ_r, hsr_eval])
                (hbty ▸ .int _)⟩
    · have hndivmod : ¬(op = TinyML.BinOp.div ∨ op = TinyML.BinOp.mod) := hdivmod
      have hΨ_ndiv :
            (do
              let t ← VerifM.expectSome
                s!"unsupported binary operator: {repr op}"
                (compileOp op sl sr)
              pure t).eval st₂ ρ_r Ψ := by
        simpa [hndivmod] using hΨ_r'
      obtain ⟨t, hcompOp, hΨ_ndiv⟩ := VerifM.eval_bind_expectSome hΨ_ndiv
      have hwfst₂ : st₂.decls.wf := (VerifM.eval.wf hΨ_ndiv).namesDisjoint
      obtain hΨ_ndiv := VerifM.eval_ret hΨ_ndiv
      have hdiv : op ≠ .div := fun h => hndivmod (Or.inl h)
      have hmod : op ≠ .mod := fun h => hndivmod (Or.inr h)
      obtain ⟨w, heval_op, hwt⟩ := evalBinOp_typed hdiv hmod htypeOf htyl htyr
      have hsl_ρ_r : sl.eval ρ_r = vl := by
        rw [Term.eval_env_agree hsl_wf (Env.agreeOn_symm hagreeOn_r)]; exact heval_l
      have ht_eval : t.eval ρ_r = w := compileOp_eval hsl_ρ_r heval_r heval_op hcompOp
      exact ⟨w, heval_op, hpost w ρ_r st₂ t hΨ_ndiv
        (compileOp_wfIn (sl.wfIn_mono hsl_wf hdecls_r hwfst₂) hsr_wf hcompOp) ht_eval (hty_eq ▸ hwt)⟩
  | letIn b e body =>
    simp only [compile] at heval
    simp only [Expr.ty] at hpost
    unfold Expr.runtime
    simp only [Runtime.Expr.letIn_subst]
    apply wp.letIn
    have heval_e_outer : (compile Θ S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compile_correct Θ e S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_e_outer) hagree hbwf hts hspec hSwf ?_
    intro v_e ρ_e st₁ se hΨ_e hse_wf heval_e htyping_e
    obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
    have hagree_e := Bindings.agreeOnLinked_env_agree hagree hagreeOn_e hbwf
    have hbwf_e : B.wf st₁.decls := fun p hp => hdecls_e.consts _ (hbwf p hp)
    obtain ⟨_, hΨ_e⟩ := VerifM.eval_bind_expectEq hΨ_e
    cases hname : b.name with
    | none =>
      simp [hname] at hΨ_e
      have hbody := compile_correct Θ body S B Γ st₁ ρ_e γ _ _
        (VerifM.eval.decls_grow ρ_e hΨ_e) hagree_e hbwf_e hts hspec hSwf
        (fun v ρ' st' se hΨ hs hw ht =>
          let ⟨_, _, hΨ'⟩ := hΨ
          hpost v ρ' st' se hΨ' hs hw ht)
      have hsubst := Runtime.Expr.subst_remove'_update' body.runtime γ Runtime.Binder.none v_e
      have hbody' :
          wp
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
      suffices wp (body.runtime.subst γ_body) Φ by
        have hsubst := Runtime.Expr.subst_remove'_update' body.runtime γ (.named x) v_e
        have hbody' :
            wp
              (Runtime.Expr.subst
                (Runtime.Subst.update' (.named x) v_e Runtime.Subst.id)
                (Runtime.Expr.subst (γ.remove' (.named x)) body.runtime))
              Φ :=
          hsubst.symm ▸ this
        rw [Binder.runtime_of_name_some hname]
        simpa [γ_body, base, Runtime.Subst.update', Runtime.Subst.update] using hbody'
      have hagreeOn_body_e : Env.agreeOn st₁.decls ρ_e ρ_body :=
        agreeOn_update_fresh_const hfresh
      have hΨ_body : (compile Θ (Finmap.erase x S) ((x, v) :: B) (Γ.extend x e.ty) body).eval st₂ ρ_body Ψ := by
        have hdecl_eval := VerifM.eval_bind _ _ _ _ hΨ_e
        have hdecl := VerifM.eval_decl hdecl_eval
        have h := hdecl v_e
        obtain h := VerifM.eval_bind _ _ _ _ h
        obtain h := VerifM.eval_assume h
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
          have : v_e = Term.eval ρ_body se := by
            rw [Term.eval_env_agree hse_wf (Env.agreeOn_symm hagreeOn_body_e)]
            exact heval_e.symm
          simpa [ρ_body, Env.updateConst] using this
      have hbwf₂ : Bindings.wf ((x, v) :: B) st₂.decls := Bindings.wf_cons hbwf_e
      have hρ_agree : Env.agreeOn (Signature.ofConsts (B.map Prod.snd)) ρ_body ρ := by
        constructor
        · intro y hy
          cases hy
        · constructor
          · intro y' hy'
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy'
            exact ((hagreeOn_e.2.1 p.2 (hbwf p hp)).trans
              (hagreeOn_body_e.2.1 p.2 (hbwf_e p hp))).symm
          · constructor <;> intro z hz <;> cases hz
      have hρ_body_lookup : ρ_body.consts .value v.name = v_e := by
        simp [ρ_body, Env.updateConst]
      have hagree_body : Bindings.agreeOnLinked ((x, v) :: B) ρ_body γ_body := by
        have h := Bindings.agreeOnLinked_cons (x := x) (γ := γ) hagree hρ_agree (hvty := (rfl : v.sort = .value))
        rwa [hρ_body_lookup] at h
      have hts_body : Bindings.typedSubst Θ ((x, v) :: B) (Γ.extend x e.ty) γ_body :=
        Bindings.typedSubst_cons hts htyping_e
      refine compile_correct Θ body (Finmap.erase x S) ((x, v) :: B) (Γ.extend x e.ty) st₂ ρ_body γ_body _ _
        (VerifM.eval.decls_grow ρ_body hΨ_body) hagree_body hbwf₂ hts_body
        (SpecMap.satisfiedBy_erase hspec) (SpecMap.wfIn_erase hSwf) ?_
      intro v' ρ' st' se' hΨ hs hw ht
      obtain ⟨_, _, hΨ'⟩ := hΨ
      exact hpost v' ρ' st' se' hΨ' hs hw ht
  | ifThenElse cond thn els ty =>
    simp only [Expr.ty] at hpost
    unfold Expr.runtime
    simp only [Runtime.Expr.subst]
    apply wp.ifThenElse
    simp only [compile] at heval
    have heval_cond : (compile Θ S B Γ cond).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compile_correct Θ cond S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_cond) hagree hbwf hts hspec hSwf ?_
    intro v_c ρ_c st₁ sc hΨ_c hsc_wf heval_c _
    obtain ⟨hdecls_c, hagreeOn_c, hΨ_c⟩ := hΨ_c
    have hagree_c := Bindings.agreeOnLinked_env_agree hagree hagreeOn_c hbwf
    have hbwf_c : B.wf st₁.decls := fun p hp => hdecls_c.consts _ (hbwf p hp)
    obtain ⟨hthn_ty, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
    obtain ⟨hels_ty, hΨ_c⟩ := VerifM.eval_bind_expectEq hΨ_c
    have heval_branches : (VerifM.all [true, false]).eval st₁ ρ_c _ := VerifM.eval_bind _ _ _ _ hΨ_c
    have hall := VerifM.eval_all heval_branches
    have htrue := hall true (by simp)
    have hfalse := hall false (by simp)
    have hwf_ne : (Formula.not (Formula.eq .value sc (.unop .ofBool (.const (.b false))))).wfIn st₁.decls := by
      simp only [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, and_true]; exact hsc_wf
    have hwf_eq : (Formula.eq .value sc (.unop .ofBool (.const (.b false) : Term .bool))).wfIn st₁.decls := by
      simp only [Formula.wfIn, Term.wfIn, Const.wfIn, UnOp.wfIn, and_true]; exact hsc_wf
    have htrue_cont := VerifM.eval_assume (VerifM.eval_bind _ _ _ _ htrue)
    have hfalse_cont := VerifM.eval_assume (VerifM.eval_bind _ _ _ _ hfalse)
    constructor
    · intro hvc_ne
      have heval_ne : sc.eval ρ_c ≠ Runtime.Val.bool false := heval_c ▸ hvc_ne
      have heval_thn : (compile Θ S B Γ thn).eval _ ρ_c Ψ :=
        htrue_cont hwf_ne (by
          simp only [Formula.eval, Term.eval, UnOp.eval, Const.denote]
          exact heval_ne)
      exact compile_correct Θ thn S B Γ _ ρ_c γ Ψ Φ heval_thn hagree_c hbwf_c hts hspec hSwf
        (fun v ρ' st' se hΨ hs hw ht => hpost v ρ' st' se hΨ hs hw (hthn_ty ▸ ht))
    · intro hvc_eq
      have heval_eq : sc.eval ρ_c = Runtime.Val.bool false := heval_c ▸ hvc_eq
      have heval_els : (compile Θ S B Γ els).eval _ ρ_c Ψ :=
        hfalse_cont hwf_eq (by
          simp only [Formula.eval, Term.eval, UnOp.eval, Const.denote]
          exact heval_eq)
      exact compile_correct Θ els S B Γ _ ρ_c γ Ψ Φ heval_els hagree_c hbwf_c hts hspec hSwf
        (fun v ρ' st' se hΨ hs hw ht => hpost v ρ' st' se hΨ hs hw (hels_ty ▸ ht))
  | app fn args aty =>
    simp only [Expr.ty] at hpost
    unfold Expr.runtime
    simp only [Runtime.Expr.subst, List.map_map]
    cases fn with
    | var f fty =>
      simp only [compile] at heval
      obtain ⟨spec, hlookup, heval⟩ := VerifM.eval_bind_expectSome heval
      obtain ⟨fval, hγf, hisPrecond⟩ := hspec f spec hlookup
      simp [Expr.runtime, Runtime.Expr.subst, hγf]
      apply wp.app
      have heval_args : (compileExprs Θ S B Γ args).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
      refine compileExprs_correct Θ args S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_args) hagree hbwf hts hspec hSwf ?_
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
      apply wp.val
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
        (fun p st' ρ' => VerifM.eval (pure p.2) st' ρ' Ψ) Φ
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
      apply hisPrecond vs htyped
      have heval_sargs_map : typedArgs.map (fun p => p.2.eval ρ_args) = vs := by
        have hsnd :
            List.map Prod.snd ((List.map Expr.ty args).zip sargs) = sargs := by
          simpa using
            (List.map_snd_zip (l₁ := List.map Expr.ty args) (l₂ := sargs)
              (Nat.le_of_eq hlen_typed.symm))
        calc
          typedArgs.map (fun p => p.2.eval ρ_args)
              = sargs.map (fun t => t.eval ρ_args) := by
                  simpa [typedArgs, List.map_map] using
                    congrArg (List.map (fun t => t.eval ρ_args)) hsnd
          _ = vs := Terms.Eval.map_eval heval_sargs
      rw [heval_sargs_map] at happly
      apply PredTrans.apply_env_agree hwf_pred _ happly
      exact Spec.argsEnv_agreeOn (Δ := Signature.empty)
        (ρ₁ := FiniteSubst.id.subst.eval ρ_args) (ρ₂ := Env.empty)
        ⟨nofun, nofun, nofun, nofun⟩ spec.args vs
        (by have := htyped.length_eq; simp [List.length_map] at this; omega)
    | _ =>
      simp only [compile] at heval
      exact (VerifM.eval_fatal heval).elim
  | tuple es =>
    simp only [Expr.ty] at hpost
    unfold Expr.runtime
    simp only [Runtime.Expr.subst, List.map_map]
    apply wp.tuple
    simp only [compile] at heval
    have heval_es : (compileExprs Θ S B Γ es).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compileExprs_correct Θ es S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_es) hagree hbwf hts hspec hSwf ?_
    intro vs ρ' st' terms hΨ hwf_terms heval_terms htyping
    obtain ⟨_, _, hΨ⟩ := hΨ
    obtain hΨ := VerifM.eval_ret hΨ
    have heval_tuple : (Term.unop .ofValList (Terms.toValList terms)).eval ρ' = Runtime.Val.tuple vs := by
      simp [Term.eval, UnOp.eval, Terms.toValList_eval heval_terms]
    have hwf_tuple : (Term.unop UnOp.ofValList (Terms.toValList terms)).wfIn st'.decls := by
      simp only [Term.wfIn]
      exact ⟨trivial, Terms.toValList_wfIn hwf_terms⟩
    exact hpost (Runtime.Val.tuple vs) ρ' st' (.unop .ofValList (Terms.toValList terms))
      hΨ hwf_tuple heval_tuple (.tuple htyping)
  | match_ scrut branches ty =>
    simp only [Expr.ty] at hpost
    unfold Expr.runtime
    simp only [Expr.branchListRuntime_eq_map, Runtime.Expr.subst, List.map_map]
    apply wp.match_
    simp only [compile] at heval
    have heval_scrut : (compile Θ S B Γ scrut).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compile_correct Θ scrut S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_scrut) hagree hbwf hts hspec hSwf ?_
    intro v_scrut ρ_scrut st_scrut se_scrut hΨ_scrut hse_wf heval_se htype_scrut
    obtain ⟨hdecls_scrut, hagreeOn_scrut, hΨ_scrut⟩ := hΨ_scrut
    cases hscrut_ty : scrut.ty with
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
            refine ⟨tag, ts.length, v_payload, ?_, ?_, ?_, ?_⟩
            · exact (Runtime.Expr.fix .none [(branches[tag]).1.runtime] (branches[tag]).2.runtime).subst γ
            · simp
            · simp [htag_branches]
            · have htag_range : tag ∈ List.range (compileBranches Θ S B Γ se_scrut ts branches 0).length := by
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
              have hbranch_wp := compileBranches_correct Θ branches S B Γ se_scrut ts.length ts 0
                st_scrut ρ_scrut γ Ψ Φ
                hagree_scrut hbwf_scrut hts hspec hSwf hse_wf
                (fun j hj v ρ' st' se hΨ hse_wf hse_eval htyped =>
                  hpost v ρ' st' se hΨ hse_wf hse_eval
                    ((htys (branches[j]) (List.getElem_mem _)) ▸ htyped))
                tag htag_branches (by simpa [Nat.zero_add, hty_eq] using heval_tag)
              simpa [Nat.zero_add] using
                hbranch_wp v_payload (by simpa [Nat.zero_add] using heval_se) (by simpa [hty_eq] using htype_payload)
        · have hΨ_bad : (VerifM.fatal "match branch type annotation mismatch").eval st_scrut ρ_scrut Ψ := by
            simpa [if_pos hlen, if_neg htys] using hΨ_scrut
          exact (VerifM.eval_fatal hΨ_bad).elim
    | _ =>
      simp [hscrut_ty] at hΨ_scrut
      exact (VerifM.eval_fatal hΨ_scrut).elim

theorem compileBranch_correct (Θ : TinyML.TypeEnv) (branch : Binder × Expr) (S : SpecMap) (B : Bindings)
    (Γ : TinyML.TyCtx) (sc : Term .value) (n i : Nat) (ty_i : TinyML.Typ)
    (st : TransState) (ρ : Env) (γ : Runtime.Subst)
    (Ψ : Term .value → TransState → Env → Prop)
    (Φ : Runtime.Val → Prop) :
    VerifM.eval (compileBranch Θ S B Γ sc n i ty_i branch) st ρ Ψ →
    B.agreeOnLinked ρ γ →
    B.wf st.decls →
    B.typedSubst Θ Γ γ →
    S.satisfiedBy Θ γ →
    S.wfIn Signature.empty →
    sc.wfIn st.decls →
    (∀ v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls →
      se.eval ρ' = v → TinyML.ValHasType Θ v branch.2.ty → Φ v) →
    ∀ payload, sc.eval ρ = Runtime.Val.inj i n payload →
      TinyML.ValHasType Θ payload ty_i →
      wp (.app ((Runtime.Expr.fix .none [branch.1.runtime] branch.2.runtime).subst γ) [.val payload]) Φ := by
  intro heval hagree hbwf hts hspec hSwf hsc_wf hpost payload hsc_eval htype_payload
  obtain ⟨binder, body⟩ := branch
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
    have hassume := VerifM.eval_assume heval_assume
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
    have hsc_eval_ρ₁ : sc.eval ρ₁ = sc.eval ρ :=
      Term.eval_env_agree hsc_wf (Env.agreeOn_symm (agreeOn_update_fresh_const hxv_fresh))
    have hformula_eval : Formula.eval ρ₁
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
    have hxv_eval : (Term.const (.uninterpreted xv.name .value)).eval ρ₁ = payload := by
      simp [Term.eval, Const.denote, ρ₁, Env.updateConst]
    have hassume_bind₂ := VerifM.eval_bind _ _ _ _ heval_assumeAll
    obtain ⟨st₂, hst₂_decls, heval_body'⟩ := VerifM.eval_assumeAll hassume_bind₂
      (fun φ hφ => typeConstraints_wfIn hxv_wf φ hφ)
      (fun φ hφ => typeConstraints_hold hxv_eval htype_payload φ hφ)
    simp only [Runtime.Expr.subst_fix, Runtime.Subst.remove'_none]
    apply wp_app_lambda_single
    show wp (Runtime.Expr.subst
      ((Runtime.Subst.update' .none Runtime.Val.unit Runtime.Subst.id).updateAll' [binder.runtime] [payload])
      (Runtime.Expr.subst ((γ.remove' .none).removeAll' [binder.runtime]) body.runtime)) Φ
    rw [Runtime.Expr.subst_fix_comp body.runtime .none [binder.runtime] γ Runtime.Val.unit [payload] rfl]
    simp only [Runtime.Subst.update']
    have hagreeOn_st : Env.agreeOn st.decls ρ ρ₁ :=
      agreeOn_update_fresh_const hxv_fresh
    cases hname : binder.name with
    | none =>
      simp [hname] at heval_body'
      have hagree₁ : B.agreeOnLinked ρ₁ γ :=
        Bindings.agreeOnLinked_env_agree hagree hagreeOn_st hbwf
      have hbwf₁ : B.wf st₂.decls := hst₂_decls ▸ fun p hp => List.Mem.tail _ (hbwf p hp)
      have hts₁ : B.typedSubst Θ (Γ.extendBinder binder ty_i) γ := by
        simpa [TinyML.TyCtx.extendBinder, hname] using hts
      have heval_body'' : (compile Θ S B (Γ.extendBinder binder ty_i) body).eval st₂ ρ₁ Ψ := by
        simpa [ρ₁, xv, hint, hname] using heval_body'
      rw [Binder.runtime_of_name_none hname]
      simpa [Runtime.Subst.update] using
        (compile_correct Θ body S B (Γ.extendBinder binder ty_i) _ ρ₁ γ Ψ Φ
          heval_body'' hagree₁ hbwf₁ hts₁ hspec hSwf (by simpa [hty] using hpost))
    | some x =>
      simp [hname, TinyML.TyCtx.extendBinder] at heval_body'
      have hagreeOn_B : Env.agreeOn (Signature.ofConsts (B.map Prod.snd)) ρ₁ ρ := by
        constructor
        · intro w hw
          cases hw
        · constructor
          · intro c hc
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
            exact (hagreeOn_st.2.1 p.2 (hbwf p hp)).symm
          · constructor <;> intro z hz <;> cases hz
      have hbwf₂ : Bindings.wf ((x, xv) :: B) st₂.decls := hst₂_decls ▸ Bindings.wf_cons hbwf
      have hρ₁_lookup : ρ₁.consts .value xv.name = payload := by
        simp [ρ₁, Env.updateConst]
      have hagree₁ : Bindings.agreeOnLinked ((x, xv) :: B) ρ₁ (Runtime.Subst.update γ x payload) := by
        have h := Bindings.agreeOnLinked_cons (x := x) (v := xv) (γ := γ) hagree hagreeOn_B (hvty := rfl)
        rwa [hρ₁_lookup] at h
      have hts₁ : Bindings.typedSubst Θ ((x, xv) :: B) (Γ.extendBinder binder ty_i) (Runtime.Subst.update γ x payload) := by
        simpa [TinyML.TyCtx.extendBinder, hname, hty] using (Bindings.typedSubst_cons hts htype_payload)
      have heval_body'' :
          (compile Θ (Finmap.erase x S) ((x, xv) :: B) (Γ.extendBinder binder ty_i) body).eval st₂ ρ₁ Ψ := by
        simpa [ρ₁, xv, hint, TinyML.TyCtx.extendBinder, hname] using heval_body'
      rw [Binder.runtime_of_name_some hname]
      simpa [Runtime.Subst.update] using
        (compile_correct Θ body (Finmap.erase x S) ((x, xv) :: B) (Γ.extendBinder binder ty_i) _ ρ₁
          (Runtime.Subst.update γ x payload) Ψ Φ heval_body'' hagree₁ hbwf₂ hts₁
          (SpecMap.satisfiedBy_erase hspec) (SpecMap.wfIn_erase hSwf) (by simpa [hty] using hpost))
  · have hexpect := VerifM.eval_bind _ _ _ _ heval
    exact False.elim (hty (VerifM.eval_expectEq hexpect).1)

theorem compileBranches_correct (Θ : TinyML.TypeEnv) (branches : List (Binder × Expr)) (S : SpecMap) (B : Bindings)
    (Γ : TinyML.TyCtx) (sc : Term .value) (n : Nat) (ts : List TinyML.Typ)
    (idx : Nat)
    (st : TransState) (ρ : Env) (γ : Runtime.Subst)
    (Ψ : Term .value → TransState → Env → Prop)
    (Φ : Runtime.Val → Prop) :
    B.agreeOnLinked ρ γ →
    B.wf st.decls →
    B.typedSubst Θ Γ γ →
    S.satisfiedBy Θ γ →
    S.wfIn Signature.empty →
    sc.wfIn st.decls →
    (∀ (j : Nat) (hj : j < branches.length) v ρ' st' se, Ψ se st' ρ' → se.wfIn st'.decls →
      se.eval ρ' = v → TinyML.ValHasType Θ v (branches[j]).2.ty → Φ v) →
    ∀ (j : Nat) (hj : j < branches.length),
      VerifM.eval (compileBranch Θ S B Γ sc n (idx + j) (ts[idx + j]?.getD .value) branches[j]) st ρ Ψ →
      ∀ payload, sc.eval ρ = Runtime.Val.inj (idx + j) n payload →
        TinyML.ValHasType Θ payload (ts[idx + j]?.getD .value) →
        wp (.app ((Runtime.Expr.fix .none [(branches[j]).1.runtime] (branches[j]).2.runtime).subst γ) [.val payload]) Φ := by
  intro hagree hbwf hts hspec hSwf hsc_wf hpost
  match branches with
  | [] =>
    intro j hj
    exact absurd hj (Nat.not_lt_zero _)
  | b :: bs =>
    intro j hj
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      intro heval
      exact compileBranch_correct Θ b S B Γ sc n idx (ts[idx]?.getD .value) st ρ γ Ψ Φ
        heval hagree hbwf hts hspec hSwf hsc_wf (by simpa using hpost 0 hj)
    | succ k =>
      have hk : k < bs.length := by simp at hj; omega
      have hidx : idx + (k + 1) = (idx + 1) + k := by omega
      simp only [hidx, List.getElem_cons_succ]
      exact compileBranches_correct Θ bs S B Γ sc n ts (idx + 1) st ρ γ Ψ Φ
        hagree hbwf hts hspec hSwf hsc_wf
        (by
          intro j hj' v ρ' st' se hΨ hse_wf hse_eval htyped
          simpa [Nat.add_assoc] using hpost (j + 1) (by simpa using hj') v ρ' st' se hΨ hse_wf hse_eval htyped)
        k hk

theorem compileExprs_correct (Θ : TinyML.TypeEnv) (es : List Expr) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) (st : TransState) (ρ : Env) (γ : Runtime.Subst)
    (Ψ : List (Term .value) → TransState → Env → Prop) (Φ : List Runtime.Val → Prop) :
    VerifM.eval (compileExprs Θ S B Γ es) st ρ Ψ →
    B.agreeOnLinked ρ γ → B.wf st.decls → B.typedSubst Θ Γ γ →
    S.satisfiedBy Θ γ → S.wfIn Signature.empty →
    (∀ vs ρ' st' terms, Ψ terms st' ρ' →
      (∀ t ∈ terms, t.wfIn st'.decls) →
      Terms.Eval ρ' terms vs →
      TinyML.ValsHaveTypes Θ vs (es.map Expr.ty) → Φ vs) →
    wps (es.map (fun e => e.runtime.subst γ)) Φ := by
  intro heval hagree hbwf hts hspec hSwf hpost
  match es with
  | [] =>
    simp only [compileExprs] at heval
    simp only [List.map, wps]
    obtain heval := VerifM.eval_ret heval
    exact hpost [] ρ st [] heval (by simp) .nil .nil
  | e :: rest =>
    simp only [compileExprs] at heval
    simp only [List.map, wps_cons]
    have heval_rest : (compileExprs Θ S B Γ rest).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compileExprs_correct Θ rest S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_rest) hagree hbwf hts hspec hSwf ?_
    intro vs ρ_vs st_vs rest_terms hΨ_vs hwf_rest heval_rest htyping_vs
    obtain ⟨hdecls_vs, hagreeOn_vs, hΨ_vs⟩ := hΨ_vs
    have hagree_vs : B.agreeOnLinked ρ_vs γ :=
      Bindings.agreeOnLinked_env_agree hagree hagreeOn_vs hbwf
    have hbwf_vs : B.wf st_vs.decls := fun p hp => hdecls_vs.consts _ (hbwf p hp)
    have heval_e : (compile Θ S B Γ e).eval st_vs ρ_vs _ := VerifM.eval_bind _ _ _ _ hΨ_vs
    refine compile_correct Θ e S B Γ st_vs ρ_vs γ _ _ (VerifM.eval.decls_grow ρ_vs heval_e) hagree_vs hbwf_vs hts hspec hSwf ?_
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
    have heval_cons : Terms.Eval ρ' (se :: rest_terms) (v :: vs) :=
      Terms.Eval.cons heval_se
        (Terms.Eval.env_agree
          (fun t ht => hwf_rest t ht)
          hagreeOn_e
          heval_rest)
    exact hpost (v :: vs) ρ' st' (se :: rest_terms) hΨ_e hwf_cons heval_cons (.cons htyping_e htyping_vs)

end

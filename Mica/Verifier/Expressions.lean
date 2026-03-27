import Mica.TinyML.Expr
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

theorem vtailN_wfIn {t : Term .vallist} {Δ : VarCtx} (ht : t.wfIn Δ) (n : Nat) :
    (vtailN t n).wfIn Δ := by
  intro v hv; rw [vtailN_freeVars] at hv; exact ht v hv

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

theorem compileUnop_wfIn {op : TinyML.UnOp} {s : Term .value} {Δ : VarCtx}
    (hs : s.wfIn Δ) {t : Term .value} (heq : compileUnop op s = some t) :
    t.wfIn Δ := by
  cases op <;> simp [compileUnop] at heq <;> subst heq <;>
    intro v hv <;> simp [Term.freeVars, vtailN_freeVars] at hv <;>
    simp_all [hs v]

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

theorem compileOp_wfIn {op : TinyML.BinOp} {sl sr : Term .value} {Δ : VarCtx}
    (hl : sl.wfIn Δ) (hr : sr.wfIn Δ) {t : Term .value} (heq : compileOp op sl sr = some t) :
    t.wfIn Δ := by
  cases op <;> simp [compileOp] at heq <;> subst heq <;>
    intro v hv <;> simp [Term.freeVars] at hv <;>
    (try cases hv) <;>
    simp_all [hl v, hr v]

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
  def compile (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) : TinyML.Expr → VerifM (TinyML.Type_ × Term .value)
    | .const (.int n)  => pure (.int,  .unop .ofInt  (.const (.i n)))
    | .const (.bool b) => pure (.bool, .unop .ofBool (.const (.b b)))
    | .const .unit     => pure (.unit, Term.const .unit)
    | .var x => do
        match B.lookup x with
        | some x' => pure (Γ x |>.getD .value, .var .value x'.name)
        | none => VerifM.fatal s!"undefined variable: {x}"
    | .unop op e => do
        let (te, se) ← compile S B Γ e
        let ty ← match TinyML.UnOp.typeOf op te with
          | some ty => pure ty
          | none => VerifM.fatal s!"type error: operator {repr op} cannot be applied to {repr te}"
        let t ← match compileUnop op se with
          | some t => pure t
          | none => VerifM.fatal s!"unsupported unary operator: {repr op}"
        pure (ty, t)
    | .assert e => do
        let (_, sl) ← compile S B Γ e
        VerifM.assert (Formula.eq .bool (Term.unop .toBool sl) (Term.const (.b true)))
        pure (.unit, Term.const .unit)
    | .binop op l r => do
        let (tl, sl) ← compile S B Γ l
        let (tr, sr) ← compile S B Γ r
        let ty ← match TinyML.BinOp.typeOf op tl tr with
          | some ty => pure ty
          | none => VerifM.fatal s!"type error: operator {repr op} cannot be applied to {repr tl} and {repr tr}"
        if op = .div ∨ op = .mod then do
          let i t := Term.unop UnOp.toInt t
          let fol_op := if op == .div then BinOp.div else BinOp.mod
          VerifM.assert (.not (.eq .int (i sr) (.const (.i 0))))
          pure (.int, Term.unop .ofInt (Term.binop fol_op (i sl) (i sr)))
        else do
          let t ← match compileOp op sl sr with
            | some t => pure t
            | none => VerifM.fatal s!"unsupported binary operator: {repr op}"
          pure (ty, t)
    | .letIn b e body => do
        let (te, se) ← compile S B Γ e
        match b with
        | .none => compile S B Γ body
        | .named x _ =>
          let x' ← VerifM.decl (some x) .value
          VerifM.assume (Formula.eq .value (.var .value x'.name) se)
          compile (Finmap.erase x S) ((x, x') :: B) (Γ.extend x te) body
    | .ifThenElse cond thn els => do
        let (_, sc) ← compile S B Γ cond
        let branch ← VerifM.all [true, false]
        if branch then do
          VerifM.assume (.not (.eq .value sc (.unop .ofBool (.const (.b false)))))
          compile S B Γ thn
        else do
          VerifM.assume (.eq .value sc (.unop .ofBool (.const (.b false))))
          compile S B Γ els
    | .app (.var f) args => do
        match S.lookup f with
        | some spec => do
          let sargs ← compileExprs S B Γ args
          Spec.call FiniteSubst.id spec sargs
        | none => VerifM.fatal s!"no spec for function {f}"
    | .tuple es => do
        let pairs ← compileExprs S B Γ es
        pure (.tuple (pairs.map Prod.fst), .unop .ofValList (Terms.toValList (pairs.map Prod.snd)))
    | .inj tag arity payload => do
        if tag ≥ arity then VerifM.fatal "inj tag out of range"
        else
          let (ty, s) ← compile S B Γ payload
          let ts := (List.replicate arity .empty).set tag ty
          pure (.sum ts, .unop (.mkInj tag arity) s)
    | .match_ scrut branches => do
        let (ty, sc) ← compile S B Γ scrut
        match ty with
        | .sum ts =>
          if ts.length ≠ branches.length then VerifM.fatal "match arity mismatch"
          else do
            let actions := compileBranches S B Γ sc ts branches 0
            let i ← VerifM.all (List.range actions.length)
            match actions[i]? with
            | some m => m
            | none => VerifM.fatal "match branch index out of range"
        | _ => VerifM.fatal "match on non-sum type"
    | .app _ _ | .fix _ _ _ _ | .ref _ | .deref _ | .store _ _ => VerifM.fatal "unsupported expression"

  /-- Compile a single match branch: assume the scrutinee is `mkInj i n payload`, then compile the body. -/
  def compileBranch (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
      (sc : Term .value) (n : Nat) (i : Nat) (ty_i : TinyML.Type_)
      : TinyML.Binder × TinyML.Expr → VerifM (TinyML.Type_ × Term .value)
    | (binder, body) => do
        let xv ← VerifM.decl (match binder with | .named x _ => some x | .none => none) .value
        VerifM.assume (.eq .value sc (.unop (.mkInj i n) (.var .value xv.name)))
        VerifM.assumeAll (typeConstraints ty_i (.var .value xv.name))
        match binder with
        | .named x ty =>
          compile (Finmap.erase x S) ((x, xv) :: B) (Γ.extendBinder (.named x ty) ty_i) body
        | .none =>
          compile S B (Γ.extendBinder .none ty_i) body

  def compileBranches (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
      (sc : Term .value) (ts : List TinyML.Type_) :
      List (TinyML.Binder × TinyML.Expr) → Nat → List (VerifM (TinyML.Type_ × Term .value))
    | [], _ => []
    | branch :: rest, i =>
      compileBranch S B Γ sc ts.length i (ts[i]?.getD .value) branch
        :: compileBranches S B Γ sc ts rest (i + 1)

  def compileExprs (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) : List TinyML.Expr → VerifM (List (TinyML.Type_ × Term .value))
    | [] => pure []
    | e :: es => do
      let rest ← compileExprs S B Γ es
      let (te, se) ← compile S B Γ e
      pure ((te, se) :: rest)
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

theorem compileBranches_spec (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx)
    (sc : Term .value) (ts : List TinyML.Type_)
    (branches : List (TinyML.Binder × TinyML.Expr)) (idx : Nat) :
    (compileBranches S B Γ sc ts branches idx).length = branches.length ∧
    ∀ j, j < branches.length →
      (compileBranches S B Γ sc ts branches idx)[j]? =
        branches[j]?.map (fun branch => compileBranch S B Γ sc ts.length (idx + j) (ts[idx + j]?.getD .value) branch) := by
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

theorem compile_correct (e : TinyML.Expr) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) (st : TransState) (ρ : Env) (γ : Runtime.Subst)
    (Ψ : TinyML.Type_ × Term .value → TransState → Env → Prop) (Φ : Runtime.Val → Prop) :
    VerifM.eval (compile S B Γ e) st ρ Ψ →
    B.agreeOnLinked ρ γ →
    B.wf st.decls →
    B.typedSubst Γ γ →
    S.satisfiedBy γ →
    S.wfIn [] →
    (∀ v ρ' st' ty se, Ψ (ty, se) st' ρ' → se.wfIn st'.decls → Term.eval ρ' se = v →
      TinyML.ValHasType v ty → Φ v) →
    wp (e.runtime.subst γ) Φ := by
  intro heval hagree hbwf hts hspec hSwf hpost
  cases e with
  | const c =>
    cases c with
    | int n =>
      simp only [compile] at heval
      simp only [TinyML.Expr.runtime, TinyML.Const.runtime, Runtime.Expr.subst_val]; apply wp.val
      obtain heval := VerifM.eval_ret heval
      exact hpost (.int n) ρ st .int _ heval
        (by intro w hw; simp [Term.freeVars] at hw)
        (by simp [Term.eval, UnOp.eval, Const.denote])
        (.int n)
    | bool b =>
      simp only [compile] at heval
      simp only [TinyML.Expr.runtime, TinyML.Const.runtime, Runtime.Expr.subst_val]; apply wp.val
      obtain heval := VerifM.eval_ret heval
      exact hpost (.bool b) ρ st .bool _ heval
        (by intro w hw; simp [Term.freeVars] at hw)
        (by simp [Term.eval, UnOp.eval, Const.denote])
        (.bool b)
    | unit =>
      simp only [compile] at heval
      simp only [TinyML.Expr.runtime, TinyML.Const.runtime, Runtime.Expr.subst_val]; apply wp.val
      obtain heval := VerifM.eval_ret heval
      exact hpost .unit ρ st .unit _ heval
        (by intro w hw; simp [Term.freeVars] at hw)
        (by simp [Term.eval])
        .unit
  | inj tag arity payload =>
    unfold TinyML.Expr.runtime; simp only [Runtime.Expr.subst]
    apply wp.inj
    simp only [compile] at heval
    by_cases htag : tag ≥ arity
    · simp [htag] at heval; exact (VerifM.eval_fatal heval).elim
    · push_neg at htag
      simp [show ¬(tag ≥ arity) from Nat.not_le.mpr htag] at heval
      have heval_p : (compile S B Γ payload).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
      refine compile_correct payload S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_p) hagree hbwf hts hspec hSwf ?_
      intro v_p ρ_p st_p ty_p se_p hΨ_p hse_wf_p heval_se_p htype_p
      obtain ⟨hdecls_p, hagreeOn_p, hΨ_p⟩ := hΨ_p
      obtain hΨ_p := VerifM.eval_ret hΨ_p
      exact hpost (.inj tag arity v_p) ρ_p st_p (.sum ((List.replicate arity .empty).set tag ty_p)) (.unop (.mkInj tag arity) se_p) hΨ_p
        (by intro w hw; simp [Term.freeVars] at hw; exact hse_wf_p w hw)
        (by simp [Term.eval, UnOp.eval, heval_se_p])
        (by
          let ts := (List.replicate arity TinyML.Type_.empty).set tag ty_p
          have hlen_ts : ts.length = arity := by simp [ts]
          have : TinyML.ValHasType (.inj tag ts.length v_p) (.sum ts) :=
            .inj (ts := ts) (by simp [ts, htag]) htype_p
          rwa [hlen_ts] at this)
  | match_ scrut branches =>
    unfold TinyML.Expr.runtime
    simp only [TinyML.Expr.branchListRuntime_eq_map, Runtime.Expr.subst, List.map_map]
    apply wp.match_
    -- Step 1: compile scrutinee (IH)
    simp only [compile] at heval
    have heval_scrut : (compile S B Γ scrut).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compile_correct scrut S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_scrut) hagree hbwf hts hspec hSwf ?_
    intro v_scrut ρ_scrut st_scrut ty_scrut se_scrut hΨ_scrut hse_wf heval_se htype_scrut
    obtain ⟨hdecls_scrut, hagreeOn_scrut, hΨ_scrut⟩ := hΨ_scrut
    -- Step 2: ty must be .sum ts
    cases ty_scrut with
    | sum ts =>
      simp at hΨ_scrut
      -- Step 3: length check must pass
      by_cases hlen : ts.length ≠ branches.length
      · simp [hlen] at hΨ_scrut
        exact (VerifM.eval_fatal hΨ_scrut).elim
      · push_neg at hlen
        simp [hlen] at hΨ_scrut
        -- Step 4: VerifM.all gives us ∀ i ∈ range, continuation holds
        have hcb := compileBranches_spec S B Γ se_scrut ts branches 0
        have hactions_len := hcb.1
        have heval_all := VerifM.eval_bind _ _ _ _ hΨ_scrut
        have hall := VerifM.eval_all heval_all
        -- Invert ValHasType v_scrut (.sum ts) to get tag, payload
        -- After cases: tag : Nat, payload : Type_ (the type at tag), t : Val (the actual payload)
        -- ht_tag : ts[tag]? = some payload, htype_payload : ValHasType t payload
        -- heval_se : se_scrut.eval ρ_scrut = Val.inj tag ts.length t
        cases htype_scrut with
        | inj ht_tag htype_payload =>
          rename_i tag ty_payload v_payload
          have htag_bound : tag < ts.length := by
            exact (List.getElem?_eq_some_iff.mp ht_tag).choose
          have htag_branches : tag < branches.length := hlen ▸ htag_bound
          refine ⟨tag, ts.length, v_payload, ?branch, ?_, ?_, ?_⟩
          case branch => exact (Runtime.Expr.fix .none [(branches[tag]).1.runtime] (branches[tag]).2.runtime).subst γ
          · rfl
          · simp [htag_branches]
          -- From hall, get the eval for branch `tag`
          have htag_range : tag ∈ List.range (compileBranches S B Γ se_scrut ts branches 0).length := by
            rw [hactions_len]; exact List.mem_range.mpr htag_branches
          have heval_tag := hall tag htag_range
          -- Rewrite actions[tag]? to compileBranch using compileBranches_correct
          have hcb_get := hcb.2 tag htag_branches
          simp [hcb_get, show branches[tag]? = some branches[tag] from List.getElem?_eq_some_iff.mpr ⟨htag_branches, rfl⟩] at heval_tag
          -- Need: ts[tag]?.getD .value = ty_payload
          have hty_eq : ts[tag]?.getD .value = ty_payload := by simp [ht_tag]
          rw [hty_eq] at heval_tag
          -- Apply compileBranches_correct (mutual) to get Forall, then project
          have hagree_scrut := Bindings.agreeOnLinked_env_agree hagree hagreeOn_scrut hbwf
          have hbwf_scrut : B.wf st_scrut.decls := fun p hp => hdecls_scrut (hbwf p hp)
          have := compileBranches_correct branches S B Γ se_scrut ts.length ts 0
            st_scrut ρ_scrut γ Ψ Φ
            hagree_scrut hbwf_scrut hts hspec hSwf hse_wf hpost
            tag htag_branches
          simp only [Nat.zero_add] at this
          rw [← hty_eq] at heval_tag
          exact this heval_tag v_payload (by rw [heval_se]) (by rw [hty_eq]; exact htype_payload)
    | _ =>
      simp at hΨ_scrut
      exact (VerifM.eval_fatal hΨ_scrut).elim
  | var x =>
    simp only [compile] at heval
    cases hbind : List.lookup x B with
    | none =>
      simp [hbind] at heval
      exact (VerifM.eval_fatal heval).elim
    | some x' =>
      simp [hbind] at heval
      unfold TinyML.Expr.runtime; simp only [Runtime.Expr.subst]
      obtain ⟨hsort, hγ⟩ := hagree x x' hbind
      rw [hγ]; simp
      apply wp.val
      have hmem : (x, x') ∈ B := by
        obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp hbind
        rw [heq]; simp
      obtain heval := VerifM.eval_ret heval
      have hwfv : (Term.var Srt.value x'.name).wfIn st.decls := by
        intro w hw; simp [Term.freeVars] at hw; subst hw
        have h := hbwf _ hmem
        cases x' with | mk n s => simp only at hsort; subst hsort; exact h
      have htyping : TinyML.ValHasType (ρ.lookup .value x'.name) (Γ x |>.getD .value) := by
        cases hΓ : Γ x with
        | none => exact .any
        | some t =>
          obtain ⟨w, hw, hwt⟩ := hts x x' t hbind hΓ
          rw [hγ] at hw
          exact (Option.some.inj hw).symm ▸ hwt
      exact hpost _ ρ st _ _ heval hwfv (by simp [Term.eval]) htyping
  | unop op e =>
    unfold TinyML.Expr.runtime; simp only [Runtime.Expr.subst]
    apply wp.unop
    simp only [compile] at heval
    have heval_e : (compile S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compile_correct e S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hts hspec hSwf ?_
    intro v_e ρ_e st₁ te se hΨ_e hse_wf heval_se htype_e
    obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
    cases htypeOf : TinyML.UnOp.typeOf op te with
    | none =>
      simp only [htypeOf] at hΨ_e
      exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ hΨ_e)).elim
    | some ty =>
      simp only [htypeOf] at hΨ_e
      cases hcompUnop : compileUnop op se with
      | none =>
        simp only [hcompUnop] at hΨ_e
        exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ hΨ_e)).elim
      | some t =>
        simp only [hcompUnop] at hΨ_e
        obtain hΨ_e := VerifM.eval_ret hΨ_e
        obtain ⟨w, heval_op, hwt⟩ := evalUnOp_typed htypeOf htype_e
        have ht_eval : t.eval ρ_e = w :=
          compileUnop_eval heval_se heval_op hcompUnop
        exact ⟨w, heval_op, hpost w ρ_e st₁ ty t hΨ_e
          (compileUnop_wfIn hse_wf hcompUnop) ht_eval hwt⟩
  | binop op l r =>
    unfold TinyML.Expr.runtime; simp only [Runtime.Expr.subst]
    apply wp.binop
    simp only [compile] at heval
    have heval_l : (compile S B Γ l).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compile_correct l S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_l) hagree hbwf hts hspec hSwf ?_
    intro vl ρ_l st₁ tyl sl hΨ_l hsl_wf heval_l htyl
    obtain ⟨hdecls_l, hagreeOn_l, hΨ_l⟩ := hΨ_l
    have hagree_l : B.agreeOnLinked ρ_l γ :=
      Bindings.agreeOnLinked_env_agree hagree hagreeOn_l hbwf
    have hbwf_l : B.wf st₁.decls := fun p hp => hdecls_l (hbwf p hp)
    have heval_r : (compile S B Γ r).eval st₁ ρ_l _ := VerifM.eval_bind _ _ _ _ hΨ_l
    refine compile_correct r S B Γ st₁ ρ_l γ _ _ (VerifM.eval.decls_grow ρ_l heval_r) hagree_l hbwf_l hts hspec hSwf ?_
    intro vr ρ_r st₂ tyr sr hΨ_r hsr_wf heval_r htyr
    obtain ⟨hdecls_r, hagreeOn_r, hΨ_r⟩ := hΨ_r
    simp only [] at hΨ_r
    cases htypeOf : TinyML.BinOp.typeOf op tyl tyr with
    | none =>
      simp only [htypeOf] at hΨ_r
      exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ hΨ_r)).elim
    | some ty =>
      simp only [htypeOf] at hΨ_r
      /- Split on whether op is division -/
      by_cases hdivmod : op = .div ∨ op = .mod
      · -- Division or modulo: both have the non-zero divisor assertion
        have hite : (op = TinyML.BinOp.div ∨ op = TinyML.BinOp.mod) = True := by simp [hdivmod]
        simp only [hite] at hΨ_r
        -- Extract past the `pure ty` bind
        have hΨ_body := VerifM.eval_ret (VerifM.eval_bind _ _ _ _ hΨ_r)
        -- From typeOf: tyl = tyr = .int, ty = .int
        rcases hdivmod with rfl | rfl <;> simp only [TinyML.BinOp.typeOf] at htypeOf
        all_goals
          cases htyl with
          | int a =>
            cases htyr with
            | int b =>
              simp at htypeOf
              have hassert_wf : (Formula.not (.eq .int (.unop .toInt sr) (.const (.i 0)))).wfIn st₂.decls := by
                intro v hv; simp [Formula.freeVars, Term.freeVars] at hv; exact hsr_wf v hv
              have heval_assert := VerifM.eval_bind _ _ _ _ hΨ_body
              have ⟨hne_zero, hΨ_post⟩ := VerifM.eval_assert heval_assert hassert_wf
              simp [Formula.eval, Term.eval, Const.denote] at hne_zero
              have hsr_eval : sr.eval ρ_r = Runtime.Val.int b := heval_r
              rw [hsr_eval] at hne_zero
              simp at hne_zero
              obtain hΨ_post := VerifM.eval_ret hΨ_post
              have hsl_ρ_r : sl.eval ρ_r = Runtime.Val.int a := by
                rw [Term.eval_env_agree hsl_wf (Env.agreeOn_symm hagreeOn_r)]; exact heval_l
              -- Reduce the `fol_op` definition (the inner `if op == .div`)
              simp (config := { decide := true }) only [] at hΨ_post ⊢
              first
              | (refine ⟨.int (a / b), ?_, ?_⟩
                 · simp [TinyML.evalBinOp, hne_zero]
                 · exact hpost (.int (a / b)) ρ_r st₂ .int _ hΨ_post
                     (by intro v hv; simp [Term.freeVars] at hv
                         rcases hv with hv | hv
                         · exact (sl.wfIn_mono hsl_wf hdecls_r) v hv
                         · exact hsr_wf v hv)
                     (by simp [Term.eval, UnOp.eval, BinOp.eval, hsl_ρ_r, hsr_eval])
                     (.int _))
              | (refine ⟨.int (a % b), ?_, ?_⟩
                 · simp [TinyML.evalBinOp, hne_zero]
                 · exact hpost (.int (a % b)) ρ_r st₂ .int _ hΨ_post
                     (by intro v hv; simp [Term.freeVars] at hv
                         rcases hv with hv | hv
                         · exact (sl.wfIn_mono hsl_wf hdecls_r) v hv
                         · exact hsr_wf v hv)
                     (by simp [Term.eval, UnOp.eval, BinOp.eval, hsl_ρ_r, hsr_eval])
                     (.int _))
            | _ => simp at htypeOf
          | _ => simp at htypeOf
      · have hndivmod : ¬(op = TinyML.BinOp.div ∨ op = TinyML.BinOp.mod) := hdivmod
        simp only [show (op = TinyML.BinOp.div ∨ op = TinyML.BinOp.mod) = False from by simp [hndivmod]] at hΨ_r
        cases hcompOp : compileOp op sl sr with
        | none =>
          simp only [hcompOp] at hΨ_r
          exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ hΨ_r)).elim
        | some t =>
          simp only [hcompOp] at hΨ_r
          obtain hΨ_r := VerifM.eval_ret hΨ_r
          have hdiv : op ≠ .div := fun h => hndivmod (Or.inl h)
          have hmod : op ≠ .mod := fun h => hndivmod (Or.inr h)
          obtain ⟨w, heval_op, hwt⟩ := evalBinOp_typed hdiv hmod htypeOf htyl htyr
          have hsl_ρ_r : sl.eval ρ_r = vl := by
            rw [Term.eval_env_agree hsl_wf (Env.agreeOn_symm hagreeOn_r)]; exact heval_l
          have ht_eval : t.eval ρ_r = w := compileOp_eval hsl_ρ_r heval_r heval_op hcompOp
          exact ⟨w, heval_op, hpost w ρ_r st₂ ty t hΨ_r
            (compileOp_wfIn (sl.wfIn_mono hsl_wf hdecls_r) hsr_wf hcompOp) ht_eval hwt⟩
  | letIn b e body =>
    simp only [compile] at heval
    cases b with
    | none =>
      unfold TinyML.Expr.runtime TinyML.Binder.runtime; simp only [Runtime.Expr.letIn_subst]
      apply wp.letIn
      have heval_e_outer : (compile S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
      refine compile_correct e S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_e_outer) hagree hbwf hts hspec hSwf ?_
      intro v_e ρ_e st₁ _ sube hΨ_e _ _ _
      obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
      simp only [Runtime.Subst.update']
      rw [show Runtime.Subst.id = (fun _ => @none Runtime.Val) from rfl, Runtime.Expr.subst_none]
      have hagree_e := Bindings.agreeOnLinked_env_agree hagree hagreeOn_e hbwf
      have hbwf_e : B.wf st₁.decls := fun p hp => hdecls_e (hbwf p hp)
      refine compile_correct body S B Γ st₁ ρ_e γ _ _ (VerifM.eval.decls_grow ρ_e hΨ_e) hagree_e hbwf_e hts hspec hSwf ?_
      grind
    | named x ty =>
      unfold TinyML.Expr.runtime TinyML.Binder.runtime; simp only [Runtime.Expr.letIn_subst]
      apply wp.letIn
      have heval_e_outer : (compile S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
      refine compile_correct e S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_e_outer) hagree hbwf hts hspec hSwf ?_
      intro v_e ρ_e st₁ te sube hΨ_e hsube_wf heval_e htyping_e
      obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
      set base := x
      set x' := fresh (addNumbers base) (st₁.decls.map Var.name)
      set v : Var := ⟨x', .value⟩
      have _hvty : v.sort = .value := rfl
      have hfresh : v.name ∉ st₁.decls.map Var.name :=
        fresh_not_mem _ _ (addNumbers_injective _)
      set st₂ : TransState :=
        { decls := v :: st₁.decls,
          asserts := (Formula.eq .value (.var .value v.name) sube) :: st₁.asserts }
      set ρ_body := ρ_e.update .value v.name v_e
      set γ_body : Runtime.Subst := Runtime.Subst.update γ x v_e
      suffices wp (body.runtime.subst γ_body) Φ by
        convert this using 1
        rw [Runtime.Expr.subst_remove'_update']
        rfl
      have hname_fresh : ∀ w ∈ st₁.decls, w.name ≠ v.name :=
        fun w hw h => hfresh (List.mem_map.mpr ⟨w, hw, h⟩)
      have hagreeOn_body_e : Env.agreeOn st₁.decls ρ_e ρ_body := by
        intro w hw
        cases w with | mk name sort =>
        simp [Env.lookup, ρ_body, Env.update]
        have hne := hname_fresh _ hw
        simp at hne
        cases sort <;> simp [hne]
      have hΨ_body : (compile (Finmap.erase x S) ((x, v) :: B) (Γ.extend x te) body).eval st₂ ρ_body Ψ := by
        obtain hΨ_e := VerifM.eval_bind _ _ _ _ hΨ_e
        obtain hΨ_e := VerifM.eval_decl hΨ_e
        have h := hΨ_e v_e
        obtain h := VerifM.eval_bind _ _ _ _ h
        obtain h := VerifM.eval_assume h
        apply h
        · intro w hw
          simp only [Formula.freeVars, List.mem_append] at hw
          rcases hw with hw | hw
          · simp [Term.freeVars] at hw; subst hw; exact List.mem_cons_self
          · exact List.mem_cons.mpr (Or.inr (hsube_wf w hw))
        · simp only [Formula.eval, Term.eval, Env.lookup_update_same]
          show v_e = Term.eval ρ_body sube
          rw [Term.eval_env_agree hsube_wf (Env.agreeOn_symm hagreeOn_body_e)]
          exact heval_e.symm
      have hbwf₁ : B.wf st₁.decls := fun p hp => hdecls_e (hbwf p hp)
      have hbwf₂ : Bindings.wf ((x, v) :: B) st₂.decls := Bindings.wf_cons hbwf₁
      have hbsnd_st : ∀ y' ∈ B.map Prod.snd, y' ∈ st.decls :=
        fun y' hm => let ⟨p, hp, heq⟩ := List.mem_map.mp hm; heq ▸ hbwf p hp
      have hρ_agree : Env.agreeOn (B.map Prod.snd) ρ_body ρ :=
        Env.agreeOn_trans
          (Env.agreeOn_symm (Env.agreeOn_mono (fun y' hm => let ⟨p, hp, heq⟩ := List.mem_map.mp hm; heq ▸ hbwf₁ p hp) hagreeOn_body_e))
          (Env.agreeOn_mono hbsnd_st (Env.agreeOn_symm hagreeOn_e))
      have hρ_body_lookup : ρ_body.lookup .value v.name = v_e := by
        simp [ρ_body, Env.lookup_update_same]
      have hagree_body : Bindings.agreeOnLinked ((x, v) :: B) ρ_body γ_body := by
        have h := Bindings.agreeOnLinked_cons (x := x) (γ := γ) hagree hρ_agree (hvty := (rfl : v.sort = .value))
        rwa [hρ_body_lookup] at h
      have hts_body : Bindings.typedSubst ((x, v) :: B) (Γ.extend x te) γ_body :=
        Bindings.typedSubst_cons hts htyping_e
      refine compile_correct body (Finmap.erase x S) ((x, v) :: B) (Γ.extend x te) st₂ ρ_body γ_body _ _ (VerifM.eval.decls_grow ρ_body hΨ_body) hagree_body hbwf₂ hts_body (SpecMap.satisfiedBy_erase hspec) (SpecMap.wfIn_erase hSwf) ?_
      grind
  | assert e =>
    unfold TinyML.Expr.runtime; simp only [Runtime.Expr.subst]
    apply wp.assert
    simp only [compile] at heval
    have heval_e : (compile S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compile_correct e S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_e) hagree hbwf hts hspec hSwf ?_
    intro v_e ρ_e st₁ te se hΨ_e hse_wf heval_se _
    obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
    let φ := Formula.eq .bool (Term.unop .toBool se) (Term.const (.b true))
    have hwf_φ : φ.wfIn st₁.decls := by
      intro v hv
      simp only [φ, Formula.freeVars, List.mem_append, Term.freeVars, List.mem_nil_iff, or_false] at hv
      exact hse_wf v hv
    have heval_assert : (VerifM.assert φ).eval st₁ ρ_e _ := VerifM.eval_bind _ _ _ _ hΨ_e
    obtain ⟨_, hcont⟩ := VerifM.eval_assert heval_assert hwf_φ
    have hΨ_pure := VerifM.eval_ret hcont
    intro _
    exact hpost .unit ρ_e st₁ .unit (Term.const .unit) hΨ_pure
      (by intro w hw; simp [Term.freeVars] at hw)
      (by simp [Term.eval])
      .unit
  | ifThenElse cond thn els =>
    unfold TinyML.Expr.runtime; simp only [Runtime.Expr.subst]
    apply wp.ifThenElse
    simp only [compile] at heval
    have heval_cond : (compile S B Γ cond).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compile_correct cond S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_cond) hagree hbwf hts hspec hSwf ?_
    intro v_c ρ_c st₁ _ sc hΨ_c hsc_wf heval_c _
    obtain ⟨hdecls_c, hagreeOn_c, hΨ_c⟩ := hΨ_c
    have hagree_c := Bindings.agreeOnLinked_env_agree hagree hagreeOn_c hbwf
    have hbwf_c : B.wf st₁.decls := fun p hp => hdecls_c (hbwf p hp)
    have heval_branches : (VerifM.all [true, false]).eval st₁ ρ_c _ := VerifM.eval_bind _ _ _ _ hΨ_c
    have hall := VerifM.eval_all heval_branches
    have htrue := hall true (by simp)
    have hfalse := hall false (by simp)
    have hwf_ne : (Formula.not (Formula.eq .value sc (.unop .ofBool (.const (.b false))))).wfIn st₁.decls := by
      intro v hv
      simp only [Formula.freeVars, List.mem_append, Term.freeVars, List.not_mem_nil, or_false] at hv
      exact hsc_wf v hv
    have hwf_eq : (Formula.eq .value sc (.unop .ofBool (.const (.b false) : Term .bool))).wfIn st₁.decls := by
      intro v hv
      simp only [Formula.freeVars, List.mem_append, Term.freeVars, List.not_mem_nil, or_false] at hv
      exact hsc_wf v hv
    have htrue_cont := VerifM.eval_assume (VerifM.eval_bind _ _ _ _ htrue)
    have hfalse_cont := VerifM.eval_assume (VerifM.eval_bind _ _ _ _ hfalse)
    constructor
    · intro hvc_ne
      have heval_ne : sc.eval ρ_c ≠ Runtime.Val.bool false := heval_c ▸ hvc_ne
      have heval_thn : (compile S B Γ thn).eval _ ρ_c Ψ :=
        htrue_cont hwf_ne (by
          simp only [Formula.eval, Term.eval, UnOp.eval, Const.denote]
          exact heval_ne)
      exact compile_correct thn S B Γ _ ρ_c γ Ψ Φ heval_thn hagree_c hbwf_c hts hspec hSwf hpost
    · intro hvc_eq
      have heval_eq : sc.eval ρ_c = Runtime.Val.bool false := heval_c ▸ hvc_eq
      have heval_els : (compile S B Γ els).eval _ ρ_c Ψ :=
        hfalse_cont hwf_eq (by
          simp only [Formula.eval, Term.eval, UnOp.eval, Const.denote]
          exact heval_eq)
      exact compile_correct els S B Γ _ ρ_c γ Ψ Φ heval_els hagree_c hbwf_c hts hspec hSwf hpost
  | app fn args =>
    unfold TinyML.Expr.runtime; simp only [Runtime.Expr.subst, List.map_map]
    cases fn with
    | var f =>
      simp only [compile] at heval
      cases hlookup : S.lookup f with
      | none =>
        simp [hlookup] at heval
        exact (VerifM.eval_fatal heval).elim
      | some spec =>
        simp [hlookup] at heval
        obtain ⟨fval, hγf, hisPrecond⟩ := hspec f spec hlookup
        simp [TinyML.Expr.runtime, Runtime.Expr.subst, hγf]
        apply wp.app
        have heval_args : (compileExprs S B Γ args).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
        refine compileExprs_correct args S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_args) hagree hbwf hts hspec hSwf ?_
        intro vs ρ_args st_args sargs hΨ_args hsargs_wf heval_sargs htyping_args
        apply wp.val
        obtain ⟨hdecls_args, hagreeOn_args, hΨ_args⟩ := hΨ_args
        have hwf_pred : spec.pred.wfIn (Spec.argVars spec.args ++ FiniteSubst.id.dom) := hSwf f spec hlookup
        have hid_wf : FiniteSubst.id.wf st_args.decls := by
          constructor
          · intro v hv; simp [FiniteSubst.id] at hv
          · exact List.nil_subset _
        have hcall := Spec.call_correct spec FiniteSubst.id sargs st_args ρ_args Ψ Φ
          hwf_pred hid_wf hsargs_wf hΨ_args
          (fun v st' ρ' t hΨ hwf heval hty => hpost v ρ' st' spec.retTy t hΨ hwf heval hty)
        obtain ⟨hsub_ty, happly⟩ := hcall
        have htyped : TinyML.ValsHaveTypes vs (spec.args.map Prod.snd) :=
          TinyML.ValsHaveTypes_sub htyping_args hsub_ty
        apply hisPrecond vs htyped
        -- Transport happly from argsEnv (id.subst.eval ρ_args) to argsEnv Env.empty
        have heval_sargs_map : sargs.map (fun p => p.2.eval ρ_args) = vs := by
          have h := heval_sargs.map_eval; simp [List.map_map] at h; exact h
        rw [heval_sargs_map] at happly
        apply PredTrans.apply_env_agree hwf_pred _ happly
        apply Spec.argsEnv_agreeOn
        · intro w hw; simp [FiniteSubst.id] at hw
        · have := htyped.length_eq; simp [List.length_map] at this; omega
    | _ =>
      simp only [compile] at heval
      exact (VerifM.eval_fatal heval).elim
  | tuple es =>
    unfold TinyML.Expr.runtime; simp only [Runtime.Expr.subst, List.map_map]
    apply wp.tuple
    simp only [compile] at heval
    have heval_es : (compileExprs S B Γ es).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compileExprs_correct es S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_es) hagree hbwf hts hspec hSwf ?_
    intro vs ρ' st' pairs hΨ hwf_pairs heval_pairs htyping
    obtain ⟨hdecls, hagreeOn, hΨ⟩ := hΨ
    obtain hdecls := hdecls
    obtain hΨ := VerifM.eval_ret hΨ
    have heval_tuple : (Term.unop .ofValList (Terms.toValList (pairs.map Prod.snd))).eval ρ' = Runtime.Val.tuple vs := by
      simp [Term.eval, UnOp.eval, Terms.toValList_eval heval_pairs]
    have hwf_tuple : (Term.unop UnOp.ofValList (Terms.toValList (pairs.map Prod.snd))).wfIn st'.decls := by
      intro w hw; simp [Term.freeVars] at hw; exact Terms.toValList_wfIn (fun t ht => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
        exact hwf_pairs p hp) w hw
    exact hpost (Runtime.Val.tuple vs) ρ' st' (.tuple (pairs.map Prod.fst)) (.unop .ofValList (Terms.toValList (pairs.map Prod.snd)))
      hΨ hwf_tuple heval_tuple (.tuple htyping)
  | fix _ _ _ _ | ref _ | deref _ | store _ _ =>
    simp only [compile] at heval
    exact (VerifM.eval_fatal heval).elim

theorem compileBranch_correct (branch : TinyML.Binder × TinyML.Expr) (S : SpecMap) (B : Bindings)
    (Γ : TinyML.TyCtx) (sc : Term .value) (n i : Nat) (ty_i : TinyML.Type_)
    (st : TransState) (ρ : Env) (γ : Runtime.Subst)
    (Ψ : TinyML.Type_ × Term .value → TransState → Env → Prop)
    (Φ : Runtime.Val → Prop) :
    VerifM.eval (compileBranch S B Γ sc n i ty_i branch) st ρ Ψ →
    B.agreeOnLinked ρ γ →
    B.wf st.decls →
    B.typedSubst Γ γ →
    S.satisfiedBy γ →
    S.wfIn [] →
    sc.wfIn st.decls →
    (∀ v ρ' st' ty se, Ψ (ty, se) st' ρ' → se.wfIn st'.decls →
      se.eval ρ' = v → TinyML.ValHasType v ty → Φ v) →
    ∀ payload, sc.eval ρ = Runtime.Val.inj i n payload →
      TinyML.ValHasType payload ty_i →
      wp (.app ((Runtime.Expr.fix .none [branch.1.runtime] branch.2.runtime).subst γ) [.val payload]) Φ := by
  intro heval hagree hbwf hts hspec hSwf hsc_wf hpost payload hsc_eval htype_payload
  obtain ⟨binder, body⟩ := branch
  simp only [compileBranch] at heval
  -- decl gives fresh variable xv
  have heval_decl := VerifM.eval_bind _ _ _ _ heval
  have hdecl := VerifM.eval_decl heval_decl
  let hint := match binder with | .named x _ => some x | .none => none
  let xv := TransState.freshVar hint .value st
  have heval_inst := hdecl payload
  -- assume sc = mkInj i n xv
  have heval_assume := VerifM.eval_bind _ _ _ _ heval_inst
  have hassume := VerifM.eval_assume heval_assume
  let st₁ : TransState := { decls := xv :: st.decls, asserts := st.asserts }
  let ρ₁ := ρ.update .value xv.name payload
  have hxv_fresh : xv.name ∉ st.decls.map Var.name :=
    fresh_not_mem _ _ (addNumbers_injective _)
  have hname_fresh : ∀ w ∈ st.decls, w.name ≠ xv.name :=
    fun w hw h => hxv_fresh (List.mem_map.mpr ⟨w, hw, h⟩)
  have hformula_wf : (Formula.eq .value sc (.unop (.mkInj i n) (.var .value xv.name))).wfIn st₁.decls := by
    intro w hw
    simp [Formula.freeVars, Term.freeVars] at hw
    rcases hw with hw | hw
    · exact List.Mem.tail _ (hsc_wf w hw)
    · subst hw; exact List.Mem.head _
  have hsc_eval_ρ₁ : sc.eval ρ₁ = sc.eval ρ := by
    apply Term.eval_env_agree hsc_wf
    intro w hw; apply Env.lookup_update_ne; left
    intro heq
    exact absurd (heq ▸ List.mem_map_of_mem (f := Var.name) hw) hxv_fresh
  have hformula_eval : Formula.eval ρ₁
      (Formula.eq .value sc (.unop (.mkInj i n) (.var .value xv.name))) := by
    simp [Formula.eval, Term.eval, UnOp.eval]
    rw [hsc_eval_ρ₁, hsc_eval]
    simp [ρ₁, Env.lookup_update_same]
  have heval_assumeAll := hassume hformula_wf hformula_eval
  -- Peel off assumeAll (typeConstraints)
  have hxv_wf : (Term.var Srt.value xv.name).wfIn st₁.decls := by
    intro w hw; simp [Term.freeVars] at hw; subst hw; exact List.mem_cons_self ..
  have hxv_eval : (Term.var Srt.value xv.name).eval ρ₁ = payload := by
    simp [Term.eval, ρ₁, Env.lookup_update_same]
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
  -- Now apply compile_correct on body (mutual recursion)
  have hagreeOn_st : Env.agreeOn st.decls ρ ρ₁ := by
    intro w hw
    cases w with | mk name sort =>
    simp [Env.lookup, ρ₁, Env.update]
    have hne := hname_fresh _ hw
    cases sort <;> simp [hne]
  cases binder with
  | none =>
    have hagree₁ : B.agreeOnLinked ρ₁ γ :=
      Bindings.agreeOnLinked_env_agree hagree hagreeOn_st hbwf
    have hbwf₁ : B.wf st₂.decls := hst₂_decls ▸ fun p hp => List.Mem.tail _ (hbwf p hp)
    exact compile_correct body S B Γ _ ρ₁ γ Ψ Φ heval_body' hagree₁ hbwf₁ hts hspec hSwf hpost
  | named x =>
    have hagreeOn_B : Env.agreeOn (B.map Prod.snd) ρ₁ ρ := by
      intro w hw
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
      exact Env.agreeOn_symm hagreeOn_st p.2 (hbwf p hp)
    have hbwf₂ : Bindings.wf ((x, xv) :: B) st₂.decls := hst₂_decls ▸ Bindings.wf_cons hbwf
    have hρ₁_lookup : ρ₁.lookup .value xv.name = payload := by
      simp [ρ₁, Env.lookup_update_same]
    have hagree₁ : Bindings.agreeOnLinked ((x, xv) :: B) ρ₁ (Runtime.Subst.update γ x payload) := by
      have h := Bindings.agreeOnLinked_cons (x := x) (v := xv) (γ := γ) hagree hagreeOn_B (hvty := rfl)
      rwa [hρ₁_lookup] at h
    have hts₁ : Bindings.typedSubst ((x, xv) :: B) (Γ.extend x ty_i) (Runtime.Subst.update γ x payload) :=
      Bindings.typedSubst_cons hts htype_payload
    exact compile_correct body (Finmap.erase x S) ((x, xv) :: B) (Γ.extend x ty_i) _ ρ₁
      (Runtime.Subst.update γ x payload) Ψ Φ heval_body' hagree₁ hbwf₂ hts₁
      (SpecMap.satisfiedBy_erase hspec) (SpecMap.wfIn_erase hSwf) hpost

theorem compileBranches_correct (branches : List (TinyML.Binder × TinyML.Expr)) (S : SpecMap) (B : Bindings)
    (Γ : TinyML.TyCtx) (sc : Term .value) (n : Nat) (ts : List TinyML.Type_)
    (idx : Nat)
    (st : TransState) (ρ : Env) (γ : Runtime.Subst)
    (Ψ : TinyML.Type_ × Term .value → TransState → Env → Prop)
    (Φ : Runtime.Val → Prop) :
    B.agreeOnLinked ρ γ →
    B.wf st.decls →
    B.typedSubst Γ γ →
    S.satisfiedBy γ →
    S.wfIn [] →
    sc.wfIn st.decls →
    (∀ v ρ' st' ty se, Ψ (ty, se) st' ρ' → se.wfIn st'.decls →
      se.eval ρ' = v → TinyML.ValHasType v ty → Φ v) →
    ∀ (j : Nat) (hj : j < branches.length),
      VerifM.eval (compileBranch S B Γ sc n (idx + j) (ts[idx + j]?.getD .value) branches[j]) st ρ Ψ →
      ∀ payload, sc.eval ρ = Runtime.Val.inj (idx + j) n payload →
        TinyML.ValHasType payload (ts[idx + j]?.getD .value) →
        wp (.app ((Runtime.Expr.fix .none [(branches[j]).1.runtime] (branches[j]).2.runtime).subst γ) [.val payload]) Φ := by
  intro hagree hbwf hts hspec hSwf hsc_wf hpost
  match branches with
  | [] => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | b :: bs =>
    intro j hj
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.getElem_cons_zero]
      intro heval
      exact compileBranch_correct b S B Γ sc n idx (ts[idx]?.getD .value) st ρ γ Ψ Φ
        heval hagree hbwf hts hspec hSwf hsc_wf hpost
    | succ k =>
      have hk : k < bs.length := by simp at hj; omega
      have hidx : idx + (k + 1) = (idx + 1) + k := by omega
      simp only [hidx, List.getElem_cons_succ]
      exact compileBranches_correct bs S B Γ sc n ts (idx + 1) st ρ γ Ψ Φ
        hagree hbwf hts hspec hSwf hsc_wf hpost k hk

theorem compileExprs_correct (es : List TinyML.Expr) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) (st : TransState) (ρ : Env) (γ : Runtime.Subst)
    (Ψ : List (TinyML.Type_ × Term .value) → TransState → Env → Prop) (Φ : List Runtime.Val → Prop) :
    VerifM.eval (compileExprs S B Γ es) st ρ Ψ →
    B.agreeOnLinked ρ γ → B.wf st.decls → B.typedSubst Γ γ →
    S.satisfiedBy γ → S.wfIn [] →
    (∀ vs ρ' st' pairs, Ψ pairs st' ρ' →
      (∀ p ∈ pairs, (p.2).wfIn st'.decls) →
      Terms.Eval ρ' (pairs.map Prod.snd) vs →
      TinyML.ValsHaveTypes vs (pairs.map Prod.fst) → Φ vs) →
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
    have heval_rest : (compileExprs S B Γ rest).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compileExprs_correct rest S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_rest) hagree hbwf hts hspec hSwf ?_
    intro vs ρ_vs st_vs rest_pairs hΨ_vs hwf_rest heval_rest htyping_vs
    obtain ⟨hdecls_vs, hagreeOn_vs, hΨ_vs⟩ := hΨ_vs
    have hagree_vs : B.agreeOnLinked ρ_vs γ :=
      Bindings.agreeOnLinked_env_agree hagree hagreeOn_vs hbwf
    have hbwf_vs : B.wf st_vs.decls := fun p hp => hdecls_vs (hbwf p hp)
    have heval_e : (compile S B Γ e).eval st_vs ρ_vs _ := VerifM.eval_bind _ _ _ _ hΨ_vs
    refine compile_correct e S B Γ st_vs ρ_vs γ _ _ (VerifM.eval.decls_grow ρ_vs heval_e) hagree_vs hbwf_vs hts hspec hSwf ?_
    intro v ρ' st' te se hΨ_e hse_wf heval_se htyping_e
    obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
    simp only at hΨ_e
    obtain hΨ_e := VerifM.eval_ret hΨ_e
    have hwf_cons : ∀ p ∈ (te, se) :: rest_pairs, (p.2).wfIn st'.decls := by
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hse_wf
      · exact fun v hv => hdecls_e (hwf_rest p hp v hv)
    have heval_cons : Terms.Eval ρ' (((te, se) :: rest_pairs).map Prod.snd) (v :: vs) :=
      Terms.Eval.cons heval_se
        (heval_rest.env_agree
          (fun t ht => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht; exact hwf_rest p hp)
          hagreeOn_e)
    exact hpost (v :: vs) ρ' st' ((te, se) :: rest_pairs)
      hΨ_e hwf_cons heval_cons (.cons htyping_e htyping_vs)

end

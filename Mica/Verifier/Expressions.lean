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
  -- CR claude: .div should be special-cased in the future: assume divisor ≠ 0
  -- as a side condition, then compile as integer division. Excluded for now
  -- because evalBinOp .div returns none on a zero divisor, and we have no
  -- mechanism to inject the non-zero assumption into the WP.
  | .div  => none
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

theorem vhead_vtailN_eval {vs : List TinyML.Val} {w : TinyML.Val} {n : Nat}
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
  | _    => none

theorem compileUnop_wfIn {op : TinyML.UnOp} {s : Term .value} {Δ : VarCtx}
    (hs : s.wfIn Δ) {t : Term .value} (heq : compileUnop op s = some t) :
    t.wfIn Δ := by
  cases op <;> simp [compileUnop] at heq <;> subst heq <;>
    intro v hv <;> simp [Term.freeVars, vtailN_freeVars] at hv <;>
    simp_all [hs v]

theorem compileUnop_eval {op : TinyML.UnOp} {s : Term .value} {ρ : Env}
    {v w : TinyML.Val} {t : Term .value}
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
  | inl | inr => simp [compileUnop] at hcomp

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
    {v1 v2 w : TinyML.Val} {t : Term .value}
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

/-- Build a `Term .vallist` from a list of `(Type_ × Term .value)` pairs. -/
def pairsToValList : List (TinyML.Type_ × Term .value) → Term .vallist
  | [] => .const .vnil
  | (_, t) :: rest => .binop .vcons t (pairsToValList rest)

@[simp] theorem pairsToValList_nil : pairsToValList [] = .const .vnil := rfl
@[simp] theorem pairsToValList_cons (t : TinyML.Type_) (s : Term .value) (rest : List (TinyML.Type_ × Term .value)) :
    pairsToValList ((t, s) :: rest) = .binop .vcons s (pairsToValList rest) := rfl

theorem pairsToValList_wfIn {pairs : List (TinyML.Type_ × Term .value)} {Δ : VarCtx}
    (h : ∀ p ∈ pairs, (p.2).wfIn Δ) : (pairsToValList pairs).wfIn Δ := by
  induction pairs with
  | nil => intro w hw; simp [pairsToValList, Term.freeVars] at hw
  | cons p rest ih =>
    simp only [pairsToValList]
    intro w hw; simp [Term.freeVars] at hw
    rcases hw with hw | hw
    · exact h p (.head _) w hw
    · exact ih (fun q hq => h q (.tail _ hq)) w hw

theorem pairsToValList_eval {pairs : List (TinyML.Type_ × Term .value)} {vs : List TinyML.Val} {ρ : Env}
    (h : List.Forall₂ (fun p v => p.2.eval ρ = v) pairs vs) :
    (pairsToValList pairs).eval ρ = vs := by
  induction h with
  | nil => simp [pairsToValList, Term.eval, Const.denote]
  | cons hhead _ ih => simp [pairsToValList, Term.eval, BinOp.eval, hhead, ih]

private theorem forall₂_eval_env_agree
    {pairs : List (TinyML.Type_ × Term .value)} {vs : List TinyML.Val} {ρ ρ' : Env} {Δ : VarCtx}
    (hwf : ∀ p ∈ pairs, (p.2).wfIn Δ)
    (hagree : Env.agreeOn Δ ρ ρ')
    (h : List.Forall₂ (fun p v => p.2.eval ρ = v) pairs vs) :
    List.Forall₂ (fun p v => p.2.eval ρ' = v) pairs vs := by
  induction h with
  | nil => exact .nil
  | @cons p v ps vs' hpv _ ih =>
    constructor
    · rw [Term.eval_env_agree (hwf p (.head _)) (Env.agreeOn_symm hagree)]; exact hpv
    · exact ih (fun q hq => hwf q (.tail _ hq))

mutual
  def compile (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) : TinyML.Expr → VerifM (TinyML.Type_ × Term .value)
    | .val (.int n)  => pure (.int,  .unop .ofInt  (.const (.i n)))
    | .val (.bool b) => pure (.bool, .unop .ofBool (.const (.b b)))
    | .val .unit     => pure (.unit, Term.const .unit)
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
        let t ← match compileOp op sl sr with
          | some t => pure t
          | none => VerifM.fatal s!"unsupported binary operator: {repr op}"
        pure (ty, t)
    | .letIn b e body => do
        let (te, se) ← compile S B Γ e
        match b with
        | .none => compile S B Γ body
        | .named x =>
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
    | .app (.var f) arg => do
        match S.lookup f with
        | some spec => do
          let (targ, sarg) ← compile S B Γ arg
          Spec.call FiniteSubst.id spec sarg targ
        | none => VerifM.fatal s!"no spec for function {f}"
    | .tuple es => do
        let pairs ← compileExprs S B Γ es
        pure (.tuple (pairs.map Prod.fst), .unop .ofValList (pairsToValList pairs))
    | .val (.inl _) | .val (.inr _) | .val (.loc _)
    | .val (.fix _ _ _ _ _) | .val (.tuple _)
    | .app _ _ | .fix _ _ _ _ _ | .ref _ | .deref _ | .store _ _ => VerifM.fatal "unsupported expression"

  def compileExprs (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) : List TinyML.Expr → VerifM (List (TinyML.Type_ × Term .value))
    | [] => pure []
    | e :: es => do
      let rest ← compileExprs S B Γ es
      let (te, se) ← compile S B Γ e
      pure ((te, se) :: rest)
end



/-! ### Correctness -/

mutual

theorem compile_correct (e : TinyML.Expr) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) (st : TransState) (ρ : Env) (γ : TinyML.Subst)
    (Ψ : TinyML.Type_ × Term .value → TransState → Env → Prop) (Φ : TinyML.Val → Prop) :
    VerifM.eval (compile S B Γ e) st ρ Ψ →
    B.agreeOnLinked ρ γ →
    B.wf st.decls →
    B.typedSubst Γ γ →
    S.satisfiedBy γ →
    S.wfIn [] →
    (∀ v ρ' st' ty se, Ψ (ty, se) st' ρ' → se.wfIn st'.decls → Term.eval ρ' se = v →
      TinyML.ValHasType v ty → Φ v) →
    wp (e.subst γ) Φ := by
  intro heval hagree hbwf hts hspec hSwf hpost
  cases e with
  | val v =>
    cases v with
    | int n =>
      simp; apply wp.val
      obtain heval := VerifM.eval_ret heval
      exact hpost (.int n) ρ st .int _ heval
        (by intro w hw; simp [Term.freeVars] at hw)
        (by simp [Term.eval, UnOp.eval, Const.denote])
        (.int n)
    | bool b =>
      simp; apply wp.val
      obtain heval := VerifM.eval_ret heval
      exact hpost (.bool b) ρ st .bool _ heval
        (by intro w hw; simp [Term.freeVars] at hw)
        (by simp [Term.eval, UnOp.eval, Const.denote])
        (.bool b)
    | unit =>
      simp; apply wp.val
      obtain heval := VerifM.eval_ret heval
      exact hpost .unit ρ st .unit _ heval
        (by intro w hw; simp [Term.freeVars] at hw)
        (by simp [Term.eval])
        .unit
    | inl _ | inr _ | loc _ | fix _ _ _ _ _ | tuple _ =>
      simp; exact (VerifM.eval_fatal heval).elim
  | var x =>
    simp only [compile] at heval
    cases hbind : List.lookup x B with
    | none =>
      simp [hbind] at heval
      exact (VerifM.eval_fatal heval).elim
    | some x' =>
      simp [hbind] at heval
      simp only [TinyML.Expr.subst]
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
    simp only [TinyML.Expr.subst]
    apply wp.unop
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
    simp only [TinyML.Expr.subst]
    apply wp.binop
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
      cases hcompOp : compileOp op sl sr with
      | none =>
        simp only [hcompOp] at hΨ_r
        exact (VerifM.eval_fatal (VerifM.eval_bind _ _ _ _ hΨ_r)).elim
      | some t =>
        simp only [hcompOp] at hΨ_r
        obtain hΨ_r := VerifM.eval_ret hΨ_r
        have hndiv : op ≠ .div := by intro h; subst h; simp [compileOp] at hcompOp
        obtain ⟨w, heval_op, hwt⟩ := evalBinOp_typed hndiv htypeOf htyl htyr
        have hsl_ρ_r : sl.eval ρ_r = vl := by
          rw [Term.eval_env_agree hsl_wf (Env.agreeOn_symm hagreeOn_r)]; exact heval_l
        have ht_eval : t.eval ρ_r = w := compileOp_eval hsl_ρ_r heval_r heval_op hcompOp
        exact ⟨w, heval_op, hpost w ρ_r st₂ ty t hΨ_r
          (compileOp_wfIn (sl.wfIn_mono hsl_wf hdecls_r) hsr_wf hcompOp) ht_eval hwt⟩
  | letIn b e body =>
    simp only [TinyML.Expr.subst]
    apply wp.letIn
    cases b with
    | none =>
      have heval_e_outer : (compile S B Γ e).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
      refine compile_correct e S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_e_outer) hagree hbwf hts hspec hSwf ?_
      intro v_e ρ_e st₁ _ sube hΨ_e _ _ _
      obtain ⟨hdecls_e, hagreeOn_e, hΨ_e⟩ := hΨ_e
      simp only [TinyML.Expr.subst_none]
      have hagree_e := Bindings.agreeOnLinked_env_agree hagree hagreeOn_e hbwf
      have hbwf_e : B.wf st₁.decls := fun p hp => hdecls_e (hbwf p hp)
      refine compile_correct body S B Γ st₁ ρ_e γ _ _ (VerifM.eval.decls_grow ρ_e hΨ_e) hagree_e hbwf_e hts hspec hSwf ?_
      grind
    | named x =>
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
      set γ_body : TinyML.Subst := TinyML.Subst.update γ x v_e
      suffices wp (body.subst γ_body) Φ by
        convert this using 1
        rw [TinyML.Expr.subst_comp]
        congr 1; funext z
        simp only [γ_body, TinyML.Subst.update, TinyML.Subst.remove'_named, TinyML.Subst.remove_eq]
        split_ifs <;> first | rfl | (cases (γ z) <;> rfl)
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
    simp only [TinyML.Expr.subst]
    apply wp.assert
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
    simp only [TinyML.Expr.subst]
    apply wp.ifThenElse
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
      have heval_ne : sc.eval ρ_c ≠ TinyML.Val.bool false := heval_c ▸ hvc_ne
      have heval_thn : (compile S B Γ thn).eval _ ρ_c Ψ :=
        htrue_cont hwf_ne (by
          simp only [Formula.eval, Term.eval, UnOp.eval, Const.denote]
          exact heval_ne)
      exact compile_correct thn S B Γ _ ρ_c γ Ψ Φ heval_thn hagree_c hbwf_c hts hspec hSwf hpost
    · intro hvc_eq
      have heval_eq : sc.eval ρ_c = TinyML.Val.bool false := heval_c ▸ hvc_eq
      have heval_els : (compile S B Γ els).eval _ ρ_c Ψ :=
        hfalse_cont hwf_eq (by
          simp only [Formula.eval, Term.eval, UnOp.eval, Const.denote]
          exact heval_eq)
      exact compile_correct els S B Γ _ ρ_c γ Ψ Φ heval_els hagree_c hbwf_c hts hspec hSwf hpost
  | app fn arg =>
    simp only [TinyML.Expr.subst]
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
        simp [TinyML.Expr.subst, hγf]
        apply wp.app
        have heval_arg : (compile S B Γ arg).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
        refine compile_correct arg S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_arg) hagree hbwf hts hspec hSwf ?_
        intro varg ρ_arg st_arg targ sarg hΨ_arg hsarg_wf heval_sarg htarg
        apply wp.val
        obtain ⟨hdecls_arg, hagreeOn_arg, hΨ_arg⟩ := hΨ_arg
        have hwf_pred : spec.pred.wfIn [⟨spec.argName, .value⟩] := hSwf f spec hlookup
        have hid_wf : FiniteSubst.id.wf st_arg.decls := by
          constructor
          · intro v hv; simp [FiniteSubst.id] at hv
          · exact List.nil_subset _
        have hcall := Spec.call_correct spec FiniteSubst.id sarg targ st_arg ρ_arg Ψ
          (fun r => TinyML.ValHasType r spec.retTy → Φ r)
          hwf_pred hid_wf hsarg_wf hΨ_arg
          (fun v st' ρ' t hΨ hwf heval hty => hpost v ρ' st' spec.retTy t hΨ hwf heval hty)
        obtain ⟨hsub_ty, happly⟩ := hcall
        have htyped : TinyML.ValHasType varg spec.argTy :=
          TinyML.ValHasType_sub htarg hsub_ty
        apply hisPrecond varg htyped
        rw [heval_sarg] at happly
        apply PredTrans.apply_env_agree hwf_pred _ happly
        intro w hw
        simp only [List.mem_singleton] at hw
        subst hw
        simp [Env.lookup_update_same]
    | _ =>
      simp only [compile] at heval
      exact (VerifM.eval_fatal heval).elim
  | tuple es =>
    simp only [TinyML.Expr.subst]
    apply wp.tuple
    have heval_es : (compileExprs S B Γ es).eval st ρ _ := VerifM.eval_bind _ _ _ _ heval
    refine compileExprs_correct es S B Γ st ρ γ _ _ (VerifM.eval.decls_grow ρ heval_es) hagree hbwf hts hspec hSwf ?_
    intro vs ρ' st' pairs hΨ hwf_pairs heval_pairs htyping
    obtain ⟨hdecls, hagreeOn, hΨ⟩ := hΨ
    obtain hΨ := VerifM.eval_ret hΨ
    have heval_tuple : (Term.unop .ofValList (pairsToValList pairs)).eval ρ' = TinyML.Val.tuple vs := by
      simp [Term.eval, UnOp.eval, pairsToValList_eval heval_pairs]
    have hwf_tuple : (Term.unop UnOp.ofValList (pairsToValList pairs)).wfIn st'.decls := by
      intro w hw; simp [Term.freeVars] at hw; exact pairsToValList_wfIn hwf_pairs w hw
    exact hpost (TinyML.Val.tuple vs) ρ' st' (.tuple (pairs.map Prod.fst)) (.unop .ofValList (pairsToValList pairs))
      hΨ hwf_tuple heval_tuple (.tuple htyping)
  | fix _ _ _ _ _ | ref _ | deref _ | store _ _ =>
    simp only [compile] at heval
    exact (VerifM.eval_fatal heval).elim

theorem compileExprs_correct (es : List TinyML.Expr) (S : SpecMap) (B : Bindings) (Γ : TinyML.TyCtx) (st : TransState) (ρ : Env) (γ : TinyML.Subst)
    (Ψ : List (TinyML.Type_ × Term .value) → TransState → Env → Prop) (Φ : List TinyML.Val → Prop) :
    VerifM.eval (compileExprs S B Γ es) st ρ Ψ →
    B.agreeOnLinked ρ γ → B.wf st.decls → B.typedSubst Γ γ →
    S.satisfiedBy γ → S.wfIn [] →
    (∀ vs ρ' st' pairs, Ψ pairs st' ρ' →
      (∀ p ∈ pairs, (p.2).wfIn st'.decls) →
      List.Forall₂ (fun p v => p.2.eval ρ' = v) pairs vs →
      TinyML.ValsHaveTypes vs (pairs.map Prod.fst) → Φ vs) →
    wps (es.map (TinyML.Expr.subst γ)) Φ := by
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
    have heval_cons : List.Forall₂ (fun p v => p.2.eval ρ' = v) ((te, se) :: rest_pairs) (v :: vs) := by
      constructor
      · exact heval_se
      · exact forall₂_eval_env_agree hwf_rest hagreeOn_e heval_rest
    exact hpost (v :: vs) ρ' st' ((te, se) :: rest_pairs)
      hΨ_e hwf_cons heval_cons (.cons htyping_e htyping_vs)

end
